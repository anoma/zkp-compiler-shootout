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

(defmacro defproc (name local stack-effect &rest body)
  "defines a miden procedure"
  (let ((keyword (intern (symbol-name name) 'keyword)))
    `(progn
       (add-function ,keyword
                     (make-procedure :name ,keyword
                                     :block (begin ,@body)
                                     :locals ,local
                                     :com (com (format nil "~{~A~^ ~}"
                                                       ',stack-effect))))
       (defun ,name ()
         (exec ,keyword)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Additional standard library functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun com (string)
  (make-com :com string))

(-> nop () instruction)
(defun nop ()
  "Acts as a no instruction in a block"
  (begin))

(-> repeat-inst (fixnum t) instruction)
(defun repeat-inst (num value)
  (apply #'begin
         (make-list num :initial-element value)))

(defun top-n-are-true (n)
  "Checks if the top n values of the stack are true
STACK EFFECT: (b₁ … bₙ -- b)"
  (repeat-inst n (mand)))

(-> load-advice-into-locals (fixnum &key (:start fixnum)) instruction)
(defun load-advice-into-locals (n &key (start 0))
  "loads n advice values off the input reel into the local argument
STACK EFFECT: (--)"
  (labels ((build-up (n current)
             (cond ((>= 0 n) (nop))
                   ;; due to this, we may wish to pad our values to
                   ;; the nearest mod 4. However we will wave that for now!
                   (t (begin
                       (adv-loadw)
                       (loc-storew current)
                       (build-up (- n 4) (+ current 4)))))))
    (begin
     ;; prepend the stack to be overwritten
     (padw)
     (build-up n start)
     (dropw))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Control Flow
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro defbegin (name arguments &body body)
  "Defines a miden block that takes common lisp arguments."
  (let ((docstring (car (remove-if-not #'stringp body)))
        (body      (remove-if #'stringp body)))
    (if docstring
        `(defun ,name ,arguments
           ,docstring
           (begin ,@body))
        `(defun ,name ,arguments
           (begin ,@body)))))

(-> repeat (fixnum &rest instruction) repeat)
(defun repeat (count &rest insturctions)
  (make-repeat :count count :block (apply #'begin insturctions)))

(-> while (&rest instruction) while)
(defun while (&rest instructions)
  (make-while :block (apply #'begin instructions)))

(-> begin (&rest (or list instruction)) block)
(defun begin (&rest instructions)
  ;; give me alambda, or give me death
  (labels ((recursive (x)
             (cond ((typep x 'block)
                    (block-to-list x))
                   ((typep x 'list)
                    (mapcan #'recursive x))
                   (t
                    (list x)))))
    (make-block :body (mapcan #'recursive instructions))))

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

(-> padw () opcode)
(defun padw ()
  "Pushes four 0 values onto the stack. Note: simple pad is not
provided because push.0 does the same thing.
STACK EFFECT: ( -- 0 0 0 0 )"
  (make-opcode :name :padw))

(-> drop () opcode)
(defun drop ()
  (make-opcode :name :drop))

(-> dropw () opcode)
(defun dropw ()
  "Deletes a word (4 elements) from the top of the stack.
STACK EFFECT: (A -- )"
  (make-opcode :name :dropw))

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
;; Input loading
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun loc-load (i)
  "Reads a word (4 elements) from local memory at index i, and pushes
the first element of the word onto the stack."
  (make-opcode :name :loc_load :constant i))

(defun loc-loadw (i)
  "Reads a word from local memory at index i and overwrites top four
stack elements with it."
  (make-opcode :name :loc_loadw :constant i))

(defun loc-store (i)
  (make-opcode :name :loc_store :constant i))

(defun loc-storew (i)
  (make-opcode :name :loc_storew :constant i))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Non deterministic Inputs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(-> push-adv (fixnum) opcode)
(defun adv-push (n)
  "Removes the next n values from advice tape and pushes them onto the stack.
Valid for n ∈ {1,...,16}. Fails if the advice tape has fewer than n
values."
  (make-opcode :name :adv_push :constant n))

(-> loadw-adv () opcode)
(defun adv-loadw ()
  "Removes the next word (4 elements) from the advice tape and
overwrites the top four stack elements with it. Fails if the advice
tape has fewer than 4 values.
STACK EFFECT: (A -- B)"
  (make-opcode :name :adv_loadw))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Merkle Operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun mtree-get ()
  (make-opcode :name :mtree.get))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-> add-n (fixnum) instruction)
(defun add-n (num)
  "Adds the n values ontop of the stack"
  (repeat-inst num (add)))

(-> add (&optional fixnum) opcode)
(defun add (&optional num)
  (make-opcode :name :add :constant num))

(-> mand () opcode)
(defun mand ()
  (make-opcode :name :and))

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
