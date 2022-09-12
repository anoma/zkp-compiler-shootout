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
;; User Facing Abstractions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro defproc (name local body)
  "defines a miden procedure"
  (let ((keyword (intern (symbol-name name) 'keyword)))
    `(progn
       (add-function ,keyword
                     (make-procedure :name ,keyword :block ,body :locals ,local))
       (defun ,name ()
         (exec ,keyword)))))

(defmacro defbegin (name arguments &body body)
  "Defines a miden block that takes common lisp arguments."
  `(defun ,name ,arguments
     (begin ,@body)))

(defun add ()
  (make-opcode :name :add))

(-> repeat (fixnum &rest instruction) repeat)
(defun repeat (count &rest insturctions)
  (make-repeat :count count :block (make-block :body insturctions)))

(-> begin (&rest instruction) block)
(defun begin (&rest instructions)
  (make-block
   :body (mapcan (lambda (x)
                   (if (typep x 'block)
                       (block-to-list x)
                       (list x)))
                 instructions)))

(defun push (item)
  (make-opcode :name :push :constant item))

(defun swap ()
  (make-opcode :name :swap))

(defun exec (name)
  (make-opcode :name :exec :constant name))

(defun dup (&optional position)
  "Dupes the value at the position on the stack, defaulting to 0 if no
value is given"
  (make-opcode :name :dup :constant position))
