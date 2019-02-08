(in-package :ab)

(def-skip-list-or-binary-tree skiplist-tree-mt
  :constructor make-skiplist-tree-mt-tree
  :reclaimer reclaim-skiplist-tree-mt-tree
  :accessor get-skiplist-tree-mt-tree
  :set-if-no-entry-given-hash set-skiplist-tree-mt-tree
  :key-deleter delete-skiplist-tree-mt-tree
  :clearer clear-skiplist-tree-mt-tree)

(defparameter insert-thread-finished t)
(defparameter delete-thread-finished t)

(defvar mt-tree (make-skiplist-tree-mt-tree))

(defun lockfree-skiplist-tree-mt-ab-test()
  (loop for values from 1 below 2 do 
	(setup-insert-thread))
  (loop for values from 1 below 2 do 
	(setup-delete-thread))
  (setup-tester-mt-tree)
  (loop for values from 1 below 2 do 
    (lisp-unit:assert-false (get-skiplist-tree-mt-tree (format nil "'key~a" values) mt-tree))))

(defun setup-insert-thread () 
  (push (list "insert-thread" ()
	      (lambda ()
		(loop for values from 1 below 2 do 
		      (setf (get-skiplist-tree-mt-tree (format nil "'key~a" values) mt-tree) values))))
	mp:*initial-processes*)
  (setf insert-thread-finished t))

(defun setup-delete-thread ()
  (push (list "delete-thread" ()
	      (lambda ()
		(loop for values from 1 below 2 do 
		      (delete-skiplist-tree-mt-tree (format nil "'key~a" values) mt-tree))))
	mp:*initial-processes*)
  (setf delete-thread-finished t))
		  
(defun setup-tester-mt-tree()
	(push (list "tester-thread" nil 'test-insert-delete)
		  mp:*initial-processes*))
		  
(defun-void test-insert-delete() 
  (sleep 30) ; let the insert and delete threads finish their job
  (mp:process-wait "waiting for threads to complete" 
		   (lambda () (and insert-thread-finished delete-thread-finished)))
  (lisp-unit:assert-true (skip-list-empty-p mt-tree))
  (clear-skiplist-tree-mt-tree mt-tree)
  (lisp-unit:assert-true (skip-list-empty-p mt-tree)))

(in-package :tests)

(defun lockfree-skiplist-tree-mt-test ()
  (ab::lockfree-skiplist-tree-mt-ab-test))

(define-test test-z-lockfree-skiplist-tree-mt
  (lockfree-skiplist-tree-mt-test)
  (format t "test lockfree-skiplist-tree-mt-test SUCCESS~%")
  (assert-true t))
