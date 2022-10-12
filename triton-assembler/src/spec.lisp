(in-package :triton)

;; Here we represent the abstract syntax of triton

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sum Type Declarations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deftype instruction ()
  `(or opcode label))

(deftype instructions ()
  `(or instruction block))

(deftype constant ()
  `(or fixnum null symbol))

(deftype instructions-list ()
  "A list of instructions"
  `(satisfies instructions-list))

(defun instructions-list (list)
  (and (listp list)
       (every (lambda (x) (typep x 'instructions)) list)))

(deftype opcode-list ()
  "A list of opcodes"
  `(satisfies opcode-list))

(defun opcode-list (list)
  (and (listp list)
       (every (lambda (x) (typep x 'opcode)) list)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Dumpable Program
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass program ()
  ((program :initarg :program
            :accessor program
            :type     list
            :initform nil)))

(defclass block ()
  ((label :initarg :label
          :type    (or null label)
          :accessor label
          :documentation "The Label of the block")
   (opcodes :initarg :opcodes
            :accessor opcodes
            :type instructions-list
            :initform nil
            :documentation "The opcodes of a block"))
  (:documentation "A block of miden code"))

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

(-> make-block (&key (:opcodes instructions-list) (:label (or null label))) block)
(defun make-block (&key opcodes label)
  (values
   (make-instance 'block :opcodes opcodes :label label)))
