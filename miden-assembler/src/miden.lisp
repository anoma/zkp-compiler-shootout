(in-package :miden)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; API functionality ontop of the system
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun block-to-list (block)
  "Turns the block into a list"
  (body block))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Extracting functionality
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-> extract ((or string pathname) &rest t) t)
(defun extract (file-name &rest instructions)
    (let ((*print-pretty*      t)
          (*print-miser-width* 70))
      (with-open-file (file file-name :direction :output
                                      :if-exists :supersede
                                      :if-does-not-exist :create)
        (format file "~{~A~^~%~%~}"
                instructions))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; User Facing Abstractions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro defproc (name local &rest body)
  "defines a miden procedure"
  (let ((keyword (intern (symbol-name name) 'keyword)))
    `(progn
       (add-function ,keyword
                     (make-procedure :name ,keyword :block (begin ,@body) :locals ,local))
       (defun ,name ()
         (exec ,keyword)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Control Flow
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro defbegin (name arguments &body body)
  "Defines a miden block that takes common lisp arguments."
  `(defun ,name ,arguments
     (begin ,@body)))

(-> repeat (fixnum &rest instruction) repeat)
(defun repeat (count &rest insturctions)
  (make-repeat :count count :block (apply #'begin insturctions)))

(-> while (&rest instruction) while)
(defun while (&rest instructions)
  (make-while :block (apply #'begin instructions)))

(-> begin (&rest instruction) block)
(defun begin (&rest instructions)
  (make-block
   :body (mapcan (lambda (x)
                   (if (typep x 'block)
                       (block-to-list x)
                       (list x)))
                 instructions)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Stack Operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-> dup (&optional fixnum) opcode)
(defun dup (&optional position)
  "Dupes the value at the position on the stack, defaulting to 0 if no
value is given"
  (make-opcode :name :dup :constant position))

(-> push (constant) opcode)
(defun push (item)
  (make-opcode :name :push :constant item))

(-> drop () opcode)
(defun drop ()
  (make-opcode :name :drop))

(-> swap (&optional fixnum) opcode)
(defun swap (&optional num)
  (make-opcode :name :swap :constant num))

(-> movup (fixnum) opcode)
(defun movup (num)
  (if (= num 1)
      (swap)
      (make-opcode :name :movup :constant num)))

(-> movdn (fixnum) opcode)
(defun movdn (num)
  (if (= num 1)
      (swap)
      (make-opcode :name :movdn :constant num)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-> add (&optional fixnum) opcode)
(defun add (&optional num)
  (make-opcode :name :add :constant num))

(-> sub (&optional fixnum) opcode)
(defun sub (&optional num)
  (make-opcode :name :sub :constant num))

(-> meq (&optional constant) opcode)
(defun meq (&optional value)
  (make-opcode :name :eq :constant value))

(-> neq (&optional constant) opcode)
(defun neq (&optional value)
  (make-opcode :name :neq :constant value))

(-> exec (keyword) opcode)
(defun exec (name)
  (make-opcode :name :exec :constant name))
