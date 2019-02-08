(in-package :ab)

(def-hash-table mt-skiplist-hashtable
  :constructor make-mt-skiplist-hashtable
  :reclaimer reclaim-mt-skiplist-hashtable
  :accessor get-mt-skiplist-hashtable
  :set-if-no-entry set-mt-skiplist-hashtable
  :key-deleter delete-mt-skiplist-hashtable
  :clearer clear-mt-skiplist-hashtable)

(defparameter put-hashtable-finished nil)
(defparameter remove-hashtable-finished nil)

(defvar mt-skiplist-hashtable (make-mt-skiplist-hashtable))

(defun lockfree-skiplist-hashtable-mt-ab-test()
  (loop for values from 1 below 2 do 
	(setup-put-hashtable))
  (loop for values from 1 below 2 do 
	(setup-remove-hashtable))
  (setup-tester-mt-skiplist-hashtable)
  (loop for values from 1 below 2 do 
    (lisp-unit:assert-false
      (get-mt-skiplist-hashtable (format nil "'key~a" values) mt-skiplist-hashtable))))
						   
(defun setup-put-hashtable() 
	(push (list "put-hashtable" ()
			(lambda ()
			  (loop for values from 1 below 2 do 
				(setf (get-mt-skiplist-hashtable (format nil "'key~a" values) mt-skiplist-hashtable) values))))
			mp:*initial-processes*)
		(setf put-hashtable-finished t))
		  
(defun setup-remove-hashtable()
	(push (list "remove-hashtable" ()
			(lambda ()
			  (loop for values from 1 above 2 do 
				(delete-mt-skiplist-hashtable (format nil "'key~a" values) mt-skiplist-hashtable))))
		  mp:*initial-processes*)
		(setf remove-hashtable-finished t))
		  
(defun setup-tester-mt-skiplist-hashtable()
	(push (list "tester-thread" nil 'test-put-remove)
		  mp:*initial-processes*))
		  
(defun-void test-put-remove() 
  (sleep 30) ; let the put and remove threads finish their job
  (mp:process-wait "waiting for threads to complete" 
		   (lambda () (and put-hashtable-finished remove-hashtable-finished)))
  (clear-mt-skiplist-hashtable mt-skiplist-hashtable)
  (lisp-unit:assert-true (skip-list-empty-p mt-skiplist-hashtable))
  (reclaim-mt-skiplist-hashtable mt-skiplist-hashtable)
  (lisp-unit:assert-true (skip-list-empty-p mt-skiplist-hashtable)))

(in-package :tests)

(defun lockfree-skiplist-hashtable-mt-test ()
  (ab::lockfree-skiplist-hashtable-mt-ab-test))

(define-test test-z-lockfree-skiplist-hashtable-mt
  (ab::lockfree-skiplist-hashtable-mt-test)
  (format t "test lockfree-skiplist-hashtable-mt-test SUCCESS~%")
  (assert-true t))
