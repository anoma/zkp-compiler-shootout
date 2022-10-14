(in-package :triton-test)

(def-suite triton
    :description "Tests the triton package")

(in-suite triton)

(def printer-test
  (block :foo
    pop
    halt
    (push 3)
    #1=(block :bar
         pop halt (push 3))
    #1#
    #1#
    (block :faz
      pop halt (push 3) pop halt (push 3) pop halt (push 3)
      pop halt (push 3) pop halt (push 3))))

(def body
  (tagbody
   :foo
     (push 3)
     (push 4)
     add
   :other
     (push 10) halt))

(def body-entry-point-no-tag
  (tagbody
     (push 3)
     (push 4)
     add
   :other
     (push 10) halt))

(def call-test
  (tagbody
     (push 3)
     (call fi)
   :fi
     return))

(defun same-name-through-gensym (x y)
  (equalp (subseq x 0 (length y)) y))

(test tagbody-works-as-expected
  (is (same-name-through-gensym (symbol-name (name (label (car (blocks body)))))
                                "foo"))
  (is (same-name-through-gensym (symbol-name (name (label (cadr (blocks body)))))
                                "other"))
  (is (equal (label (car (blocks body-entry-point-no-tag))) nil))
  (is (same-name-through-gensym
       (symbol-name (constant (car (last (opcodes (car (blocks call-test)))))))
       "fi")))

(test printer-works-as-expected
  (let ((*print-pretty* t))
    (is (equalp (format nil "~A" printer-test)
"foo:
  pop halt push 3
bar:
  pop halt push 3
bar:
  pop halt push 3
bar:
  pop halt push 3
faz:
  pop
  halt
  push 3
  pop
  halt
  push 3
  pop
  halt
  push 3
  pop
  halt
  push 3
  pop
  halt
  push 3"))))
