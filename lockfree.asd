(in-package :cl-user)

(defpackage #:cl-lockfree.system
  (:use :common-lisp :asdf))
 
(in-package :cl-lockfree.system)

(defsystem #:lockfree
  :description "A library of portable lock-free data structures in Common Lisp"
  :version "1.0"
  :author "Chun Tian (binghe) <binghe.lisp@gmail.com>"
  :license "MIT"
  :components
  ((:file "package")
   (:file "utils"       :depends-on ("package"))
   (:file "queue"      :depends-on ("utils"))))

(defsystem #:lockfree.tests
  :description "Unit test of lockfree data structures"
  :depends-on (:portable-threads)
  :components
  ((:file "test-queue")))
