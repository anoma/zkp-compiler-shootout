(in-package :miden)

(defparameter *table* (make-hash-table :test #'eq))

(defun add-function (name object)
  (setf (gethash name *table*) object))

(defun lookup-function (name)
  (gethash name *table*))
