(in-package :triton)


;; First attempt

;; Improvmenets to make
;; 1. Functions should automatically place a tag

;; _Meta Comment_
;; Since we lack gotos, we approach the challenge, in the following way.
;; do a test, if it works, then call. the call then does a return.
;; recurse
;; if the test fails, then skip the call, then call the exit branch.

;; Note :: None of this is needed, trying to setup general recursion
;; technique though, this will show.

(def fib-general
  (tagbody
   :fib-entry
     ;; setup the fib accumulator values and call then return
     (push 1) (push 0) (call :fib-body) return
   :fib-body
     ;; dup the n from the top of the stack and check against 0
     (dup 2)
     skiz (call :fib-then)
     (dup 2)
     skiz recurse
     return
   :fib-then
     ;; compute a + b, b and n -1
     (dup 1) add (swap 2) (push -1) add
     ;; move the values such that we have (n a b -- a b n)
     (swap 2) (swap 1) return))

(def program
  (make-program :program
                (list*
                 ;; let's just take the input as public for now
                 (push 50)
                 (call :fib-entry)
                 fib-general)))

;; control function
(defun fibonacci (n &optional (a 0) (b 1))
  (if (zerop n)
      a
      (fibonacci (1- n) b (+ a b))))


(defun dump ()
  (extract "triton/fib.tasm" program))
