(in-package :miden)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Fibonacci
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; we can't call ourselves recursively is an issue, I'd have to
;; maintain a stack with a loop point!
(defproc fib_rec 0 (--))

(-> loop-check-sub (&key (:pos fixnum) (:by fixnum)) instruction)
(defbegin loop-check-sub (&key pos by)
  "STACK EFFECT: ( ... a -- a ... a )"
  (movup pos) (sub by) (dup) (movdn (1+ pos)))

(defproc fib_iter 0 (iteration-amount -- fib-answer)
  ;; setup the starting values!
  (push 0)
  (push 1)
  ;; move back our starting value
  (dup 2)
  (neq 0)
  (com "Looks about 8 cyles every loop")
  (while (swap) (dup 1) (add) (loop-check-sub :pos 2 :by 1) (neq 0))
  ;; clean up the pushes, otherwise rust throws a fit
  (drop) (swap) (drop))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Fibonacci Fixed looping
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defbegin fib (n)
  (com "Looks about 3 cyles every loop, since the repeat can be inlined away")
  (repeat n (swap) (dup 1) (add)))

(defproc fib_100 0 (i j -- k)
  (fib 100))

;; Control Function
(defun fibonacci (n &optional (a 0) (b 1))
  (if (zerop n)
      a
      (fibonacci (1- n) b (+ a b))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sudoku
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Let us make the complicated Sudoku program. we can do it the simple
;; way by providing the data in the advice tape, which is the private
;; input set. We are going to store the values in the locals
;; _INEFFICIENCIES LIST_:
;; 1. we do a `(movup (- 4 (1- n)))', we can do (- 4 (- n 2)) for
;;    commutative operations and save a cycle

(defbegin fold-n-locals (binary-function local-location n)
  "Folds `n' locals at the given `local-location' with the given `binary-function'
Note that the top four stack elements are overwritten by the locals
STACK EFFECT: (a₁ a₂ a₃ a₄ acc -- answer b₁ b₂ b₃ b₄)"
  (loc-loadw local-location)
  (if (>= 4 n)
      (begin (repeat-inst (1- n) binary-function)
             (movup (- 4 (1- n)))
             binary-function
             (repeat-inst n (dup)))
      (begin (repeat-inst 4 binary-function)
             (padw)
             (fold-n-locals binary-function (+ 4 local-location) (- n 4)))))

(-> rows-add-up (unsigned-byte &key (:pad boolean) (:size unsigned-byte)) instruction)
(defbegin rows-add-up (i &key (pad nil) (size 9))
  "Checks if the row `i' adds to the expected value
STACK EFFECT: pad    = ( -- answer p1 p2 p3 p4)
              no-pad = (d1 d2 d3 d4 -- answer p1 p2 p3 p4)"
  ;; Start the accumulator at 0
  (push 0)
  (if pad (padw) (movdn 4))
  ;; grab the row values and reduce them
  (fold-n-locals (add) (* size i) size)
  ;; check if they are equal to the expected answer
  (sudoku-should-add-up-to size))

(defun sudoku-should-add-up-to (size)
  "Checks if the sudoku values add up given the `size' of the board"
  (meq (apply #'+ (alexandria:iota size :start 1))))

(-> columns-add-up (fixnum &key (:size fixnum)) instruction)
(defbegin columns-add-up (i &key (size 9))
  "Check of the column `i' adds to the epxected value
STACK EFFECT: ( -- answer)"
  ;; This will be inefficient, as we are doing 9 separate 4 instruction loads.
  (mapcar #'loc-load (alexandria:iota size :start i :step size))
  (repeat-inst (1- size) (add))
  (sudoku-should-add-up-to size))

(defun find-starting-index (i size)
  (mvlet ((square-size   (sqrt size))
          (div remainder (floor i (sqrt size))))
    (round
     (+ (* div (* square-size size))
        (* square-size remainder)))))

;; TODO make size matter in the terms of loads!
(-> rows-add-up (unsigned-byte &key (:pad boolean) (:size unsigned-byte)) instruction)
(defun squares-add-up (i &key (size 9) (pad nil))
  "Checks if the square `i' adds to the expected value
STACK EFFECT: pad    = ( -- answer p1 p2 p3 p4)
              no-pad = (d1 d2 d3 d4 -- answer p1 p2 p3 p4)"
  (let ((starting-index (find-starting-index i size)))
    (begin
     ;; Start the accumulator at 0
     (push 0)
     (if pad (padw) (nop))
     (mapcar (lambda (index)
               (list (movdn 4) (fold-n-locals (add) index 3)))
             (alexandria:iota 3 :start starting-index :step size))
     (sudoku-should-add-up-to size))))

(defun check (check &key ((:size n) 9) (needs-padding t))
  "Takes a check function that overwrites the top of the stack and
checks if the conditions hold. The function returns a boolean whether
it passed or not. `needs-padding' determines if the function needs a
word of padding to operate efficiently or not.
STACK EFFECT: (-- b)"
  (assert (= (expt (round (sqrt n)) 2) n))
  (begin
   (if needs-padding (padw) (nop))
   (mapcar (lambda (i)
             (begin (funcall check i)
                    (if needs-padding (movdn 4) (nop))))
           (alexandria:iota n))
   (if needs-padding (dropw) (nop))
   (com "let us check the values are all true!")
   (top-n-are-true (1- n))))

;; _INEFFICIENCIES LIST_:
;; 1. We do 27 `loc-loadw' values, when we can get away with 21 in `rows-add-up'
;; 2. we could avoid `rows-add-up' by just duping the top word and doing
;;    column check there.
;; 3. we write into locals which are 3-4 cycles each.
;;   whereas if I tried it with memory addresses it would be 1
;;   cycle instead of 3-4, however Ι would maybe leak the data if I
;;   did? I need to test both versions I think.
;; Trade Off Notes:
;; 1. We prefer live sudoku puzzles. Meaning we pay extra for false
;;    ones, as we always compute the full checks without returing early
;; Random Notes:
;; we can do this much more efficiently, however we need to rethink
;; our algorithm given our tools.  Namely we re-read many locations,
;; where we can instead just do computation faster. Like
;; `load-advice-into-locals' can serve as the read-column check
(defproc sudoku 84 (-- verfied?)
  (load-advice-into-locals 81)
  (com "we do our 27 loads for the rows adding up to the correct number")
  (check #'rows-add-up :needs-padding t :size 9)
  (com "we do 81 loads for the columns adding up to the correct number")
  (check #'columns-add-up :needs-padding nil :size 9)
  (mand)
  (com "we do our 27 loads for the squares adding up to the correct number")
  (check #'squares-add-up :needs-padding t :size 9)
  (mand))

(defun dump ()
  (extract
   "miden/fib.masm"
   (lookup-function :fib_iter)
   (begin
    (fib_iter)))
  (extract
   "miden/sudoku.masm"
   (lookup-function :sudoku)
   (begin
    (sudoku)))
  (extract
   "miden/fib100.masm"
   (lookup-function :fib_100)
   (begin (fib_100)))
  (extract
   "miden/fib50.masm"
   (fib 50))
  (extract
   "miden/fib1000.masm"
   (fib 1000))
  (extract
   "miden/fib92.masm"
   (fib 92))
  (extract
   "miden/fib93.masm"
   (fib 93))
  (extract
   "miden/fib94.masm"
   (fib 94)))
