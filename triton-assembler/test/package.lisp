(defpackage :triton-test
  ;; I really want to use mix, but alas Ι don't want to assume a
  ;; newer asdf for sbcl
  (:shadowing-import-from :triton
   :prod :case :tagbody :block :begin :drop :push :pop :return :call)
  (:use #:serapeum #:cl #:triton #:fiveam)
  (:local-nicknames)
  (:export #:run-tests))

(in-package :triton-test)
