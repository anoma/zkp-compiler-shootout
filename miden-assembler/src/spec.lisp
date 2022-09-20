(in-package :miden)

;; Here we represent the abstract syntax of miden

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sum Type Declarations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deftype instruction ()
  `(or opcode repeat block while com))

(deftype constant ()
  `(or fixnum null symbol))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Statement Product Types
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass procedure ()
  ((name :initarg :name
         :type    keyword
         :accessor name
         :documentation "Name of the procedure")
   (locals :initarg  :locals
           :type     fixnum
           :accessor locals
           :initform 0
           :documentation
           "number of memory locals")
   (block :initarg :block
          :accessor block
          :type     block)
   (com :initarg :com
        :accessor comm
        :type     (or null com))))

(defclass block ()
  ((body :initarg :body
         :accessor body
         :type list)))

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

(defclass repeat ()
  ((count :initarg  :count
          :type     fixnum
          :accessor count
          :initform 0
          :documentation
          "Executing a sequence of instructions a predefined number of times")
   (block :initarg :block
          :accessor block
          :type     block)))

(defclass while ()
  ((block :initarg :block
          :accessor block
          :type     block))
  (:documentation "A conditional controlled loop in Miden"))

(defclass com ()
  ((com :initarg :com
        :accessor comm
        :type     string))
  (:documentation "A comment in Miden"))

(defclass mif ()
  ()
  (:documentation "An if expression in Miden"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructors for the base types
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-> make-block (&key (:body list)) block)
(defun make-block (&key body)
  (values
   (make-instance 'block :body body)))

(-> make-procedure (&key (:name keyword) (:locals fixnum) (:block block) (:com (or null com)))
    procedure)
(defun make-procedure (&key name block locals com)
  (values
   (make-instance 'procedure :block block :name name :locals locals :com com)))

(-> make-opcode (&key (:name keyword) (:constant constant)) opcode)
(defun make-opcode (&key name (constant nil))
  (values
    (make-instance 'opcode :name name :constant constant)))

(-> make-repeat (&key (:count fixnum) (:block block)) repeat)
(defun make-repeat (&key count block)
  (values
   (make-instance 'repeat  :block block :count count)))

(-> make-while (&key (:block block)) while)
(defun make-while (&key block)
  (values
   (make-instance 'while :block block)))

(-> make-com (&key (:com string)) com)
(defun make-com (&key com)
  (values
   (make-instance 'com :com com)))
