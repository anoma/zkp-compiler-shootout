(in-package :miden)

;; Here we represent the abstract syntax of miden

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sum Type Declarations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Statement Product Types
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Not sure how useful this is
(defclass block ()
  ((body :initarg :body
         :accessor body
         :type list)))

(defclass procedure ()
  ((name :initarg :name
         :type    keyword
         :accessor name
         :documentation "Name of the procedure")
   (block :initarg :block
          :accessor :block
          :type      block)))

(deftype constant ()
  `(or fixnum null))

(defclass opcode ()
  ((name :initarg :name
         :type    keyword
         :accessor name
         :documentation "Name of the opcode")
   (constant :initarg  :constant
             :accessor constant
             :type     constant
             :initform nil
             :documentation "extra constant input argument if any exists")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructors for the base types
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-> make-block (&key (:body list)) block)
(defun make-block (&key body)
  (values
   (make-instance 'block :body body)))

(-> make-procedure  (&key (:name keyword) (:block block)) block)
(defun make-procedure (&key name block)
  (values
   (make-instance 'block :block block :name name)))

(-> make-opcode  (&key (:name keyword) (:constant constant)) opcode)
(defun make-opcode (&key name (constant nil))
  (values
    (make-instance 'opcode :name name :constant constant)))
