(in-package :triton)

;; Should we really use deflex here? This means Ι can't easily later
;; use mutable methods for constructing values, without giving up on
;; the deflex macro.

;; Further this means labels must use keywords.

;; However, using plane words may be more idiomatic from a stack POV

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; API Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmacro tagbody (&body code)
  `(list
    ,@(mapcar (lambda (x)
                (cons 'block x))
              (group-by #'keywordp code))))

(tagbody
 :foo
   (push 3) (push 4) add
 :other
   (push 10) halt)

(-> block-to-list (block) opcode-list)
(defun block-to-list (block)
  "Turns the block into a list"
  (opcodes block))

(-> block ((or keyword label) &rest (or list instructions)) block)
(defun block (label &rest instructions)
  (make-block :label   (if (keywordp label) (make-label :name label) label)
              :opcodes (opcodes (apply #'begin instructions))))

(-> begin (&rest (or list instruction block)) block)
(defun begin (&rest instructions)
  (labels ((recursive (x)
             (cond ((and (typep x 'block) (null (label x)))
                    (block-to-list x))
                   ((typep x 'list)
                    (mapcan #'recursive x))
                   (t
                    (list x)))))
    (make-block :opcodes (mapcan #'recursive instructions))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; OpCodes from the Triton Specification
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Stack Operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(-> push (constant) opcode)
(defun push (n)
  "Pushes a onto the stack."
  (make-opcode :name :push :constant n))

(-> dup (&optional constant) opcode)
(defun dup (&optional n)
  "Duplicates the element i positions away from the top, assuming 0 <= i < 16."
  (make-opcode :name :dup :constant n))

(-> swap (&optional constant) opcode)
(defun swap (&optional n)
  "Swaps the ith stack element with the top of the stack, assuming 0 < i < 16."
  (make-opcode :name :swap :constant n))

(def pop (make-opcode :name :pop)
  "Pops top element from stack.")

(def divine (make-opcode :name :divine)
  "Pushes a non-deterministic element a to the stack. Interface for secret input.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Control Flow
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def nop (make-opcode :name :nop)
  "Do nothing")

(def skiz (make-opcode :name :skiz)
  "Skip next instruction if a is zero. s ∈ {1, 2, 3} depends on a and
whether or not next instruction takes an argument.")

(-> call (constant) opcode)
(defun call (n)
  "Push (o+2,d) to the jump stack, and jump to absolute address d"
  (make-opcode :name :call :constant n))

(def return (make-opcode :name :return)
  "Pop one pair off the jump stack and jump to that pair's return
address (which is the first element).")

(def recurse (make-opcode :name :recurse)
  "Peek at the top pair of the jump stack and jump to that pair's
destination address (which is the second element).")

(def assert (make-opcode :name :assert)
  "Pops a if a == 1, else crashes the virtual machine.")

(def halt (make-opcode :name :halt)
  "Solves the halting problem (if the instruction is reached). Indicates
graceful shutdown of the VM.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Arithmetic on Stack
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def add (make-opcode :name :add))
