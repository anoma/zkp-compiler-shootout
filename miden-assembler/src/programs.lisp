(in-package :miden)

(defbegin fib (n)
  (repeat n
   (swap)
   (dup 1)
   (add)))

(defproc fib_100 0
  (fib 100))

(defun fibonacci (n &optional (a 0) (b 1))
  (if (zerop n)
      a
      (fibonacci (1- n) b (+ a b))))

(defun dump ()
  (extract
   "miden/fib.masm"
   (lookup-function :fib_100)
   (begin (push 0)
          (push 1)
          (fib_100)
          (fib 1000)))
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
