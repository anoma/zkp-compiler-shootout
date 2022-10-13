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

(def rot
  (begin (swap 2) (swap 1))
  "STACK EFFECT: (n a b -- a b n)")

(def fib-general
  (tagbody
   :fib-entry
     ;; setup the fib accumulator values and call then return
     (push 1)
     (push 0)
     (call :fib-body)
     return
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
     ;; move the stack back how we found it (n a b -- a b n)
     rot return))

(def program
  (make-program :program
                (list
                 (begin
                  ;; let's just take the input as public for now
                  (push 50)
                  (call :fib-entry)
                  fib-general))))

;; control function
(defun fibonacci (n &optional (a 0) (b 1))
  (if (zerop n)
      a
      (fibonacci (1- n) b (+ a b))))

(defun dump ()
  (extract "triton/fib.tasm" program))

;; Leaving this code in. This will be useful if we get gotos in
;; triton. Even if not, this can hopefully inspire another strategy
;; for getting if's working like I'd want. Maybe we can flip it, and
;; have a way to get recrusion on one side working without gotos.
;; Further this nudges us into properly defining label combination see
;; #16

;; (defun if (then else)
;;   (let ((name-then (intern (symbol-name (gensym)) :keyword))
;;         (name-else (intern (symbol-name (gensym)) :keyword))
;;         (name-cont (intern (symbol-name (gensym)) :keyword)))
;;     (begin
;;      skiz
;;      (goto name-then)
;;      (goto name-else)
;;      (add-label name-then then)
;;      (goto name-cont)
;;      (add-label name-else else)
;;      (goto name-cont)
;;      (make-label :name name-cont))))

;; ;; defproc will just place an implicit label to the whole block, so
;; ;; the return goes to it
;; (defproc fib (n -- n)
;;   (push 1) (push 0) (call fib-general) return)

;; (defproc fib-general (a b n -- n)
;;   (dup 2)
;;   (if (begin (dup 1) add (swap 2) (push -1) add rot recruse)
;;       return))
