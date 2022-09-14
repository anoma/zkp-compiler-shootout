(in-package :miden)

(defbegin fib (n)
  (repeat n (swap) (dup 1) (add)))

(defproc fib_100 0
  (fib 100))

(defun fibonacci (n &optional (a 0) (b 1))
  (if (zerop n)
      a
      (fibonacci (1- n) b (+ a b))))

(defproc fib_rec 0
  )

(defproc fib_iter 0
  ;; setup the starting values!
  (push 0)
  (push 1)
  ;; move back our starting value
  (dup 2)
  (neq 0)
  (while (swap) (dup 1) (add) (loop-check-sub :pos 2 :by 1) (neq 0)))

(-> loop-check-sub (&key (:pos fixnum) (:by fixnum)) instruction)
(defbegin loop-check-sub (&key pos by)
  (movup pos) (sub by) (dup) (movdn (1+ pos)))

(defun dump ()
  (extract
   "miden/fib.masm"
   (lookup-function :fib_iter)
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
