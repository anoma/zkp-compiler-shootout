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

;; TODO ∷ Memory isn't continuous like I'd expect, thus Ι have to
;;        treat each load like a vector, rather than a memory address
;;        offset. Thus

;; NOTE ∷ The data must be padded to the nearest word with 0's

;; Let us make the complicated Sudoku program. we can do it the simple
;; way by providing the data in the advice tape, which is the private
;; input set. We are going to store the values in the locals
;; _INEFFICIENCIES LIST_:
;; 1. we do a `(movup (- 4 (1- n)))', we can do (- 4 (- n 2)) for
;;    commutative operations and save a cycle

(defbegin fold-n-local-words (binary-function local-location n)
  "Folds `n' local words at the given `local-location' with the given
`binary-function' Note that the top word of the stack are overwritten
by the loads.
STACK EFFECT: (a₁ a₂ a₃ a₄ acc -- answer 0 0 0 0)"
  ;; we could make this faster by duping instead of padding, as it
  ;; removes a movup
  (mapcar (lambda (i)
            (begin
             (loc-loadw i)
             (repeat-inst 4 binary-function)
             (padw)))
          (alexandria:iota n :start local-location))
  (movup 4))

(-> rows-add-up (unsigned-byte &key (:pad boolean) (:size unsigned-byte)) instruction)
(defbegin rows-add-up (i &key (pad nil) (size 3))
  "Checks if the row `i' adds to the expected value
STACK EFFECT: pad    = ( -- answer p1 p2 p3 p4)
              no-pad = (d1 d2 d3 d4 -- answer p1 p2 p3 p4)"
  ;; Start the accumulator at 0
  (push 0)
  (if pad (padw) (movdn 4))
  ;; grab the row values and reduce them
  (fold-n-local-words (add) (* size i) size)
  ;; check if they are equal to the expected answer
  (sudoku-should-add-up-to size))

(defun sudoku-should-add-up-to (size)
  "Checks if the sudoku values add up given the `size' of the board"
  (meq (apply #'+ (alexandria:iota (expt size 2) :start 1))))

(-> columns-add-up (fixnum &key (:pad boolean) (:size fixnum)) instruction)
(defbegin columns-add-up (i &key (pad nil) (size 3))
  "Check of the column `i' adds to the epxected value
STACK EFFECT: pad    = ( -- answer p1 p2 p3 p4)
              no-pad = (d1 d2 d3 d4 -- answer p1 p2 p3 p4)"
  ;; This will be inefficient, as we are doing 9 separate 4 word
  ;; loads, to pick out what we need!.
  ;; We could save this by doing this in batches of 3, and having 3
  ;; answers
  (push 0)
  (if pad (padw) (movdn 4))
  (mapcar (lambda (i)
            (mvlet* ((div word-offset-normal-order (floor i size))
                     ;; Words are the other endian so have to flip the loading
                     (word-offest-big-endian-order (- 3 word-offset-normal-order)))
              (begin
               (loc-loadw div)                      ; load the word
               (movup word-offest-big-endian-order) ; move the number down
               (movup 4)                            ; move the accumulator
               (add)                                ; now add them!
               (movdn 3)                            ; don't let it be overwritten
               (push 100))))
          (alexandria:iota (expt size 2) :start i :step (expt size 2)))
  (movup 4)                             ; this call can be avoided
  (sudoku-should-add-up-to size))

(-> rows-add-up (unsigned-byte &key (:pad boolean) (:size unsigned-byte)) instruction)
(defun squares-add-up (i &key (size 3) (pad nil))
  "Checks if the square `i' adds to the expected value
STACK EFFECT: pad    = ( -- answer p1 p2 p3 p4)
              no-pad = (d1 d2 d3 d4 -- answer p1 p2 p3 p4)"
  (mvlet* ((div-col offset-row (floor i size))
           ;; we times it by 9 because we are offsetting 3 rows of
           ;; arrays for every 3 that we go down. the offset
           ;; corresponds to the offset within the relative column
           ;; area
           (correct-square (+ (* div-col 9) offset-row)))
    (begin
     ;; Start the accumulator at 0
     (push 0)
     (if pad (padw) (movup 4))
     (mapcar (lambda (index)
               (begin (loc-loadw index)
                      (repeat-inst 4 (add))
                      (padw)))
             (alexandria:iota size :start correct-square :step size))
     (movup 4)
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

;; 1. In `rows-add-up' we could go with a total of 21 load-words
;;    instead of 27, however that requires not padding the array. It
;;    should be investigated if that method is faster.
;; 2. We could make the `columns-add-up' more efficient, by adding 3
;;    rows at a time a time, we can do 1 load, and add all relevant
;;    numbers properly.
;; 3. we write into locals which are 3-4 cycles each.
;;    whereas if I tried it with memory addresses it would be 1
;;    cycle instead of 3-4, however Ι would maybe leak the data if I
;;    did? I need to test both versions I think.
;;
;; Trade Off Notes:
;; 1. We prefer live sudoku puzzles. Meaning we pay extra for false
;;    ones, as we always compute the full checks without returing early
;; 2. We pad the array, meaning we take up more space, but makes the
;;    logic a bit easier to implement. I'm unsure if this is more or
;;    less efficient
;;
;; Random Notes:
;; we can do this much more efficiently, however we need to rethink
;; our algorithm given our tools.  Namely we re-read many locations,
;; where we can instead just do computation faster. Like
;; `load-advice-into-locals' can serve as the read-column check
(defproc sudoku 27 (-- verfied?)
  (loadw-advice-into-locals 27)
  (com "we do our 27 word loads for the rows adding up to the correct number")
  (check #'rows-add-up :needs-padding t :size 9)
  (com "we do 81 word loads for the columns adding up to the correct number")
  (check #'columns-add-up :needs-padding t :size 9)
  (mand)
  (com "we do our 27 word loads for the squares adding up to the correct number")
  (check #'squares-add-up :needs-padding t :size 9)
  (mand))

(defproc trying 27 (A -- A)
  ;; loads don't work like you think
  (loadw-advice-into-locals 1)
  (com "they are in reverse order than you would think!")
  (loc-loadw 0))

(defun dump ()
  (extract
   "miden/fib.masm"
   (lookup-function :fib_iter)
   (begin
    (fib_iter)))
  (extract
   "miden/sudoku.masm"
   (lookup-function :sudoku)
   (begin (sudoku)))
  (extract
   "miden/trying.masm"
   (lookup-function :trying)
   (begin (trying)))
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
