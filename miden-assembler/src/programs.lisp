(in-package :miden)

(defbegin fib (n)
  (repeat n
   (swap)
   (dup 1)
   (add)))

(defproc fib_100 0
  (fib 100))

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
   (begin (fib_100))))
