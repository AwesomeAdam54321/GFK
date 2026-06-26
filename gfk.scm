;; Copyright (C) 2026 Adam Faiz
;; This file is part of GFK.
;;
;; GFK is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; GFK is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GFK If not, see <http://www.gnu.org/licenses/>.

(define-module (gfk)
  #:use-module (ice-9 match)
  #:use-module (srfi srfi-1)
  #:use-module (scheme base)
  #:use-module (rnrs bytevectors)
  #:use-module (rnrs io ports)
  #:use-module (hashing crc))

(define (int->bytes n size)
  (let loop ((lst '()) (x n) (s size))
    (if (zero? s)
	(u8-list->bytevector lst)
	(loop (cons (logand x #xff) lst) (ash x -8) (1- s)))))

(define* (str->bytes str #:optional (size #f))
  (let* ((str-bv (string->bytevector str (make-transcoder (utf-8-codec))))
	 (n (bytevector-length str-bv))
	 (padding (make-bytevector (if size (- size n) 0))))
    (bytevector-append str-bv padding)))

(define* (offset n #:optional (m 0)) (+ (* n 4096) m))
(define (disk-write port offset bv)
  (seek port offset SEEK_SET)
  (put-bytevector port bv))

(define-crc crc-64)
(define (checksum port offset)
  (seek port offset SEEK_SET)
  (let ((bv (bytevector-append (get-bytevector-n port 4088)
			       (make-bytevector 8))))
    (int->bytes (crc-64 bv) 8)))

(define-syntax define-field
  (syntax-rules ()
    ((_ block (r start size))
     (define (r port)
       (let* ((bv (make-bytevector size))
	      (_ (get-bytevector-n! port bv (offset block start) size)))
	 bv)))
    ((_ block (r w start size))
     (begin
       (define-field block (r start size))
       (define (w port bv)
	 (if (= (bytevector-length bv) size)
	     (disk-write port (offset block start) bv)
	     (error "Invalid field data" 'w bv)))))))

(define-syntax within-block
  (syntax-rules ()
    ((_ n slice)
     (define-field n slice))
    ((_ n slice slice* ...)
     (begin (define-field n slice)
	    (within-block n slice* ...)))))

(within-block 0
  (boot:jmp #x000 3)
  (boot:bytes/sector boot:sector-size #x003 2)
  (boot:reserved-size #x005 1)
  (boot:sectors/block boot:sectors #x006 1)
  (boot:media-type boot:media #x007 1)
  (boot:total-blocks boot:blocks #x008 8)
  (boot:disk-id #x010 8)
  (boot:byte-order boot:endianness #x018 4)
  (boot:code #x01c 482)
  (boot:sig boot:signature #x1fe 2)
  (boot:reserved #x200 3584))

(define *actions* '())
(define-syntax within-block*
  (syntax-rules ()
    ((_ n syms slice slice* ...)
     (begin
       (define-field n slice)
       (within-block* n syms slice* ...)))
    ((_ n (action action* ...))
     (begin
       (set! *actions* (acons 'action action *actions*))
       (within-block* n (action* ...))))
    ((_ n ())
     (begin
       (let ((these-actions (alist-copy *actions*)))
	 (set! *actions* '())
	 (lambda (action-name . args)
	   (apply (assq-ref these-actions action-name) args)))))))

(define-syntax-rule (define-block name syms slice slice* ...)
  (define (name n) (within-block* n syms slice slice* ...)))

(define-block block
  (block-id tag id version count name-length name ptrs checksum
   block-idd tagged idd versioned counted
   name-lengthened named ptrsd checksummed)
  (block-id block-idd #x000 8)
  (tag tagged #x008 4)
  (id idd #x00c 6)
  (version versioned #x012 2)
  (count counted #x014 8)
  (name-length name-lengthened #x01c 1)
  (name named #x1d 251)
  (ptrs ptrsd #x118 3808) ; max 238 checksummed blocks
  (checksum checksummed #xff8 8))

(define dir block)
(define file block)

(define-block ext-block
  (block-id tag type ext-id version ptrs checksum)
  (block-id #x000 8)
  (tag #x008 4)
  (type #x00c 4)
  (ext-id #x010 6)
  (version #x016 2)
  (ptrs #x018 4064) ; max 254 checksummed blocks
  (checksum #xff8 8))

(define-block data-block
  (block-id tag type seq data checksum)
  (block-id #x000 8)
  (tag #x008 4)
  (type #x00c 4)
  (seq #x010 8)
  (data #x018 4064)
  (checksum #xff8 8))

(define-block free-block
  (block-type tag data checksum)
  (block-type #x000 8)
  (tag #x008 4)
  (data #x00c 4076)
  (checksum #xff8 8))

(define-block bad-block
  (block-id data)
  (block-id #x000 8)
  (data #x008 4088))

(define tags '((dir  . #u8(#x4c #x44 #x45 #x52))
	       (file . #u8(#x46 #x49 #x4c #x45))
	       (ext  . #u8(#x45 #x58 #x54 #x44))
	       (data . #u8(#x44 #x41 #x54 #x41))
	       (bad  . #u8(#xff #xff #xff #xff))
	       (free . #u8(#x00 #x00 #x00 #x00))))

(define* (init-boot to #:optional (max-blocks 1024))
  (define fixed-disk #u8(#xf8))
  (define big-endian #u8(#x42 #x49 #x47 #x45))
  (put-bytevector to (make-bytevector (offset max-blocks)))
  (boot:sector-size to #u8(#x10 #x00))
  (boot:sectors to #u8(#x00))
  (boot:media to fixed-disk)
  (boot:blocks to (int->bytes max-blocks 8))
  (boot:endianness to big-endian)
  (boot:signature to #u8(#xaa #x55)))

(define* (make-dir to #:key
		   (block 1) (tag 'dir) (block-id 1) (id 0) (version 0)
		   (count 0) (name "[M.F.D:/]") (ptrs #f))
  (define b (file block))
  (b 'block-idd to (int->bytes block-id 8))
  (b 'tagged to (assq-ref tags tag))
  (b 'idd to (int->bytes id 6))
  (b 'versioned to (int->bytes version 2))
  (b 'counted to (int->bytes count 8))
  (b 'name-lengthened to (u8-list->bytevector (list (string-length name))))
  (b 'named to (str->bytes name 251))
  (when ptrs (b 'ptrsd to ptrs))
  (b 'checksummed to (checksum to (offset block))))

(define (init-img file)
  (system* "touch" file)
  (let ((port (open-file file "r+")))
    (init-boot port)
    (make-dir port)))

(init-img "disk.img")
