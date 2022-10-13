(in-package :triton)

;; Should we really use deflex here? This means Ι can't easily later
;; use mutable methods for constructing values, without giving up on
;; the deflex macro.

;; Further this means labels must use keywords.

;; However, using plane words may be more idiomatic from a stack POV

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Extracting functionality
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-> extract ((or string pathname) &rest t) t)
(defun extract (file-name &rest instructions)
  (let ((*print-pretty* t))
    (with-open-file (file file-name :direction :output
                                    :if-exists :supersede
                                    :if-does-not-exist :create)
      (format file "~{~A~^~:@_~:@_~}"
              instructions))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; API Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmacro tagbody (&body code)
  "Creates jump tables for triton code. The idiomatic way to create
blocks and labels."
  `(begin
    ,@(mapcar (lambda (x) (if (keywordp x) `(make-label :name ,x) x)) code)))

(-> block ((or keyword label) &rest (or list instructions)) tlabels)
(defun block (label &rest instructions)
  (values
   (apply #'begin
          (cons (if (keywordp label) (make-label :name label) label)
                instructions))))

(-> begin (&rest (or list instructions)) tlabels)
(defun begin (&rest instructions)
  (mvfoldr #'cons-instructions-to-labels
           (alexandria:flatten instructions)
           (make-labels)))
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
(def mul (make-opcode :name :mul))

(def teq (make-opcode :name :eq))
