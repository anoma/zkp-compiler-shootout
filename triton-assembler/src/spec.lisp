(in-package :triton)

;; Here we represent the abstract syntax of triton

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sum Type Declarations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deftype instruction ()
  `(or opcode label))

(deftype constant ()
  `(or fixnum null symbol))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Dumpable Program
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass program ()
  ((program :initarg :program
            :accessor program
            :type     list
            :initform nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Instruction Product Types
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defclass label ()
  ((name :initarg :name
         :type    keyword
         :accessor name
         :documentation "Label to jump to")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructors for the base types
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-> make-opcode (&key (:name keyword) (:constant constant)) opcode)
(defun make-opcode (&key name (constant nil))
  (values
    (make-instance 'opcode :name name :constant constant)))

(-> make-label (&key (:name keyword) (:constant constant)) label)
(defun make-label (&key name)
  (values
    (make-instance 'label :name name)))

(-> make-program (&key (:program list)) program)
(defun make-program (&key program)
  (values
   (make-instance 'program :program program)))
