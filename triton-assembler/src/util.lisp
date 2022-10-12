(in-package :triton)

(defun group-by (predicate list)
  (labels ((recurse (list current-group groups)
             (cond ((null list)
                    (reverse (cons (reverse current-group)
                                   groups)))
                   ((funcall predicate (car list))
                    (recurse (cdr list)
                             (list (car list))
                             (cons (reverse current-group)
                                   groups)))
                   (t
                    (recurse (cdr list)
                             (cons (car list) current-group)
                             groups)))))
    (when list
      (recurse (cdr list) (list (car list)) nil))))
