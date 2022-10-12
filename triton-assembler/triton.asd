(asdf:defsystem :triton
  :depends-on (:trivia :alexandria :serapeum)
  :version "0.0.1"
  :description "A qucik and dirty Assembler for tritonVM"
  :author "Mariari"
  :license "MIT"
  :pathname "src/"
  :components
  ((:file package)
   (:file spec     :depends-on (package))
   (:file printer  :depends-on (package spec))
   (:file triton   :depends-on (package spec))
   (:file table    :depends-on (package spec))
   (:file programs :depends-on (package spec triton table)))
  :in-order-to ((asdf:test-op (asdf:test-op :triton/test))))


(asdf:defsystem :triton/test
  :depends-on (:triton :fiveam)
  :description "Testing triton"
  :pathname "test/"
  :serial t
  :components
  ((:file "package")
   (:file "triton")
   (:file "run-tests"))
  :perform (asdf:test-op (o s)
                         (uiop:symbol-call :triton-test :run-tests)))
