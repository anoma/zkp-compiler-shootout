;; We use CL streams as they are much better for concatenating to, and
;; have us worry less. they are a mutable interface however.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FORMAT RUNDOWN FOR THOSE WHO ARE UNFAMILIAR
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; https://www.cs.cmu.edu/Groups/AI/html/cltl/clm/node257.html

;; DSL FOR NEWLINES AND CONTROL OF IT

;; ~4I  = (pprint-indent :block   4)
;; ~4:I = (pprint-indent :current 4)
;; ~_   = (pprint-newline :linear)
;; ~@_  = (pprint-newline :miser)
;; ~:@_ = (pprint-newline :mandatory)
;; ~:_  = (pprint-newline :fill)


;; FOR PRINTING NORMALLY NOTE THESE TAKE ARGUMENTS!

;; ~(~a~)    = print symbol lower case instead of upper case
;; ~{~A~}    = prints a list element by element.

;; ~{~A~^ ~} = prints a list element by element, the last element of
;;             the list does not print the extra space
;; EXAMPLE:
;; CL-USER> (format nil "~{~A~^ ~}" (list 1 2 3 4 5))
;; "1 2 3 4 5"
;; CL-USER> (format nil "~{~A ~}" (list 1 2 3 4 5))
;; "1 2 3 4 5 "

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; TopLevel Extraction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :miden)

(-> extract (list &optional stream) stream)

(defmethod print-object ((op opcode) stream)
  (format stream "~(~a~)" (name op))
  (when (constant op)
    (format stream ".~(~a~)" (constant op))))

(defmethod print-object ((obj block) stream)
  (pprint-logical-block (stream nil)
    (format stream "begin ~2I~:@_")
    (block-as-list obj stream)
    (format stream "~0I~:@_end")))

(defmethod print-object ((obj repeat) stream)
  (pprint-logical-block (stream nil)
    (pprint-indent :current 2 stream)
    (format stream "repeat.~A~2I~:@_ " (count obj))
    (block-as-list (block obj) stream)
    (format stream " ~0I~:@_end")))

(defun block-as-list (block stream)
  (pprint-logical-block (stream nil)
    (format stream "~{~A~^ ~_~}" (block-to-list block))))


;; REMOVΕ once I get a test case up
;; (make-block :body
;;             (list (make-opcode :name :input :constant 3)
;;                   (make-opcode :name :input :constant 5)
;;                   (make-opcode :name :add)))

;; (make-repeat :count 5
;;              :block
;;              (make-block :body (list (make-opcode :name :input :constant 100)
;;                                      (make-opcode :name :input :constant 200))))

;; (make-block :body (list (make-opcode :name :input :constant 3)
;;                         (make-opcode :name :input :constant 5)
;;                         (make-repeat :count 5
;;                                      :block
;;                                      (make-block :body (list (make-opcode :name :input :constant 100)
;;                                                              (make-opcode :name :input :constant 200))))
;;                         (make-opcode :name :add)))
