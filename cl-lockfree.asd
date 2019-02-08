;;;; -*- Mode: Lisp -*-
;;;;
;;;; See the LICENSE file for licensing information.

(in-package :asdf)

(defsystem #:cl-lockfree
  :description "A portable library of lock-free data structures"
  :version (:read-file-form "version.sexp")
  :author "Chun Tian (binghe)"
  :license "MIT"
  :depends-on (:portable-threads)
  :components
  ((:file "package")
   (:file "utilities"           :depends-on ("package"))
   (:file "constant-queue"      :depends-on ("utilities"))
   (:file "skip-list"           :depends-on ("utilities"))
   ))

(defsystem #:cl-lockfree.tests
  :description "Unit test of lockfree data structures"
  :version (:read-file-form "version.sexp")
  :author "Chun Tian (binghe)"
  :license "MIT"
  :depends-on (cl-lockfree)
  :components
  ((:module "tests"
    :components
    ((:file "test-constant-queue")
     (:file "test-skip-list")))))

(defmethod perform ((op test-op) (c (eql (find-system #:cl-lockfree))))
  (oos 'load-op #:cl-lockfree.tests)
  (oos 'test-op #:cl-lockfree.tests))
