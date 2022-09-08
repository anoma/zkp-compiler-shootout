(asdf:defsystem :miden-assembler
  :depends-on (:trivia :alexandria :serapeum)
  :version "0.0.1"
  :description "A qucik and dirty Assembler for miden-VM"
  :author "Mariari"
  :license "MIT"
  :pathname "src/"
  :build-pathname "../build/alu.image"
  :entry-point "alu::main"
  :build-operation ;; #+(or ecl ccl)
  "program-op"
  ;; #-(or ecl ccl) "image-op"
  :components
  ((:file package)
   (:file spec  :depends-on (package))
   (:file miden :depends-on (package spec))))
