(in-package :miden)

;; Control Function
(defun fibonacci (n &optional (a 0) (b 1))
  (if (zerop n)
      a
      (fibonacci (1- n) b (+ a b))))

;; we can't call ourselves recursively is an issue, I'd have to
;; maintain a stack with a loop point!
(defproc fib_rec 0 (--))

(-> loop-check-sub (&key (:pos fixnum) (:by fixnum)) instruction)
(defbegin loop-check-sub (&key pos by)
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
  (movdn 2) (drop) (drop))

(defbegin fib (n)
  (com "Looks about 3 cyles every loop, since the repeat can be inlined away")
  (repeat n (swap) (dup 1) (add)))

(defproc fib_100 0 (i j -- k)
  (fib 100))

;; Let us make the complicated Sudoku program. we can do it the simple
;; way by providing the data in the advice tape, which is the private
;; input set. We are going to store the values in the locals

;; TODO :: Should I really write it to locals. they are 3-4 cycles,
;;         were as if I tried it with memory addresses it would be 1
;;         cycle instead, however Ι would maybe leak the data if I
;;         did? I need to test both versions I think.

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

(-> rows-add-up (fixnum &key (:pad boolean) (:size fixnum)) instruction)
(defun rows-add-up (i &key (pad nil) (size 9))
  "Checks if the row `i' adds to the expected value
STACK EFFECT: pad    = ( -- answer p1 p2 p3 p4)
              no-pad = (d1 d2 d3 d4 -- answer p1 p2 p3 p4)"
  (assert (> size 0))
  (labels ((reduce-values (start n)
             (begin (loc-loadw start)
                    (if (>= 4 n)
                        (begin
                         (add-n n)
                         (repeat-inst n (push 0))
                         (movup n))
                        (begin
                         (add-n 4)
                         (padw)
                         (reduce-values (+ 4 start) (- n 4)))))))
    (begin
     ;; Start the accumulator at 0
     (push 0)
     (if pad (padw) (movdn 4))
     ;; grab the column values and reduce them
     (reduce-values (* size i) size)
     ;; check if they are equal to the expected answer
     (meq (apply #'+ (alexandria:iota size :start 1))))))

(-> columns-add-up (fixnum &key (:size fixnum)) instruction)
(defun columns-add-up (i &key (size 9))
  "Check of the column `i' adds to the epxected value
STACK EFFECT: pad    = ( -- answer p1 p2 p3 p4)
              no-pad = (d1 d2 d3 d4 -- answer p1 p2 p3 p4)"
  size i
  ;; This will be inefficient
  (begin
   ;; Start the accumulator at 0
   (push 0)
   ))

(defun check (check &key ((:size n) 9) (needs-padding t))
  "Takes a check function that overwrites the top of the stack and
checks if the conditions hold. The function returns a boolean whether
it passed or not. `needs-padding' determines if the function needs a
padding of words to operate efficiently or not.
STACK EFFECT: (-- b)"
  (assert (= (expt (round (sqrt n)) 2) n))
  (begin
   (if needs-padding (padw) (nop))
   (apply #'begin
          (mapcar (lambda (i)
                    (begin (funcall check i)
                           (if needs-padding (movdn 4) (nop))))
                  (alexandria:iota 9)))
   (if needs-padding (dropw) (nop))
   (com "let us check the values are all true!")
   (top-n-are-true (1- n))))

;; Inefficiencies List
;; 1. We do 27 `loc-loadw' values, when we can get away with 21 in `rows-add-up'
;; 2. we could avoid `rows-add-up' by just duping the top word and doing
;;    column check there.
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
  (check #'columns-add-up :needs-padding nil :size 9))

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
    (fib_iter)))
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
