(in-package :triton)

;; Here we represent the abstract syntax of triton

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sum Type Declarations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(deftype instructions ()
  "instructions and their groups"
  `(or instruction block tlabels))

(deftype instruction ()
  "An instruction in tritonVM"
  `(or opcode label))

(deftype constant ()
  `(or fixnum null symbol))

(deftype instructions-list ()
  "A list of instructions in tritonVM"
  `(satisfies instructions-list))

(deftype opcode-list ()
  "A list of opcodes in tritonVM"
  `(satisfies opcode-list))

(deftype block-list ()
  "A list of blocks in tritonVM"
  `(satisfies block-list))

(defun opcode-list (list)
  (and (listp list)
       (every (lambda (x) (typep x 'opcode)) list)))

(defun block-list (list)
  (and (listp list)
       (every (lambda (x) (typep x 'block)) list)))

(defun instructions-list (list)
  (and (listp list)
       (every (lambda (x) (typep x 'instructions)) list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Dumpable Program
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass program ()
  ((program :initarg :program
            :accessor program
            :type     list
            :initform nil)))

(defclass procedure ()
  ((calls :initarg :calls
          :type    list
          :accessor calls
          :documentation "The call graph of the procedure")
   (name :initarg :name
         :type    keyword
         :accessor name
         :documentation "Name of the procedure")
   (tlabels :initarg :blocks
            :type    tlabels
            :accessor tlabels
            :initform (make-labels)
            :documentation "the labels of the procedure")))

;; another lens into the procedure
(defmethod blocks ((proc procedure))
  (blocks (tlabels proc)))

;; change the representation to get better speed, it's sad that we do
;; O(n) operations for this.
(defclass tlabels ()
  ((blocks :initarg :blocks
           :type    block-list
           :accessor blocks))
  (:documentation "A series of Blocks in Miden code, may or may not be ordered"))

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

(-> make-label (&key (:name keyword)) label)
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

(-> make-labels (&key (:blocks list)) tlabels)
(defun make-labels (&key blocks)
  (values
   (make-instance 'tlabels :blocks blocks)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helper functions to manipulate the types
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-> block-to-list (block) opcode-list)
(defun block-to-list (block)
  "Turns the block into a list"
  (values
   (opcodes block)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helper functions to check on labels
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-> no-label-on-front-blockp (tlabels) boolean)
(defun no-label-on-front-blockp (lb)
  "returns true if the front block exists and there is no label for it"
  (and (blocks lb) (not (label (car (blocks lb))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helper functions to Cons multiple instructions onto a structure
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-> cons-instructions-to-labels (instructions tlabels) tlabels)
(defun cons-instructions-to-labels (insts labels)
  "Adds `instructions' to the given `tlabels'."
  (values
   (etypecase-of instructions insts
     (instruction (cons-instruction insts labels))
     (tlabels     (mvfoldr #'cons-instructions-to-labels (blocks insts) labels))
     (block       (let ((blks (blocks labels)))
                    (make-labels
                     :blocks
                     (cond ((not blks)         (list insts))
                           ((label (car blks)) (cons insts blks))
                           (t                  (cons (append-blocks insts (car blks))
                                                     (cdr blks))))))))))

(-> append-blocks (block block) block)
(defun append-blocks (b1 b2)
  "Appends two blocks, assuming the right block does not have a label"
  (when (label b2)
    (error "the second block in an append should not have a label"))
  (make-block :label (label b1)
              :opcodes (append (opcodes b1)
                               (opcodes b2))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helper functions to Cons a single instructions onto a structure
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgeneric cons-instruction (instruction place)
  (:documentation "Adds a given instruction to the front of the given place."))

(defmethod cons-instruction (instruction (lb tlabels))
  (flet ((add-onto (first-block blocks)
           (cons (cons-instruction instruction first-block) blocks)))
    (let ((blocks (blocks lb)))
      (make-labels :blocks (if (no-label-on-front-blockp lb)
                               (add-onto (car blocks) (cdr blocks))
                               (add-onto (make-block) blocks))))))

(defmethod cons-instruction ((op opcode) (bl block))
  (make-block :label (label bl)
              :opcodes (cons op (opcodes bl))))

(defmethod cons-instruction ((lb label) (bl block))
  (if (label bl)
      (error "currently don't know how to combine multiple label")
      (make-block :label lb
                  :opcodes (opcodes bl))))
