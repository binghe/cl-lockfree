(in-package :cl-user)

(defpackage #:cl-lockfree.system
  (:use :common-lisp :asdf))
 
(in-package :cl-lockfree.system)

(defsystem #:cl-lockfree
  :description "A library of portable lock-free data structures in Common Lisp"
  :version "1.0"
  :author "Chun Tian (binghe) <binghe.lisp@gmail.com>"
  :license "MIT"
  :depends-on (:portable-threads)
  :components
  ((:file "package")
   (:file "utilities"     :depends-on ("package"))
   (:file "lockfree-list" :depends-on ("utilities"))))

(defsystem #:cl-lockfree.tests
  :description "Unit test of lockfree data structures"
  :depends-on (cl-lockfree)
  :components
  ((:module "tests"
    :components
    ((:file "test-lockfree-list")))))
