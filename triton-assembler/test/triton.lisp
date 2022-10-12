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

(test tagbody-works-as-expected
  (is (equal (name (label (car body))) :foo))
  (is (equal (name (label (cadr body))) :other)))

(test printer-works-as-expected
  (let ((*print-pretty* t))
    (is (equalp (format nil "~A" printer-test)
"foo:
  pop
  halt
  push 3
  bar: pop halt push 3
  bar: pop halt push 3
  bar: pop halt push 3
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
