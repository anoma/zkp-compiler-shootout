(in-package :triton-test)

(defparameter *all-tests*
  (list 'triton))

(defun run-tests ()
  (mapc #'run! *all-tests*))
