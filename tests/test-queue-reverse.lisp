;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was written at
;;;; Carnegie Mellon University and released into the public domain. The
;;;; software is in the public domain and is provided with absolutely no
;;;; warranty. See the COPYING and CREDITS files for more information.

;;;; Same test as in test-queue.lisp, but use PushLeft and PopRight.

;;;; (run-tests '(queue.tr.1 queue.tr.2 queue.tr.3))

(in-package :tests)

;;; Test subject: parallel enqueue, single dequeue
;;; Used APIs:
;;;   AB::MAKE-EMPTY-CONSTANT-QUEUE
;;;   AB::CONSTANT-QUEUE-PUSH-LEFT
;;;   AB::CONSTANT-QUEUE-POP-RIGHT

#+(and SymScale LispWorks)
(define-test queue.tr.1 ; parallel enqueue, single dequeue
  (let* ((q (ab::make-empty-constant-queue))
	 (w (mp:make-semaphore :name "w" :count 0))
	 (r (mp:make-semaphore :name "r" :count 0))
	 (n 100000)
	 (schedulers
	  (list (mp:process-run-function "thread 1" ()
		  #'(lambda ()
		      (let ((ab::current-thread-index 1))
			(mp:semaphore-release r)
			(mp:semaphore-acquire w) ; wait for main thread
			(dotimes (i n)
			  (ab::constant-queue-push-left q (cons :a i))))))
		(mp:process-run-function "thread 2" ()
		  #'(lambda ()
		      (let ((ab::current-thread-index 2))
			(mp:semaphore-release r)
			(mp:semaphore-acquire w) ; wait for main thread
			(dotimes (i n)
			  (ab::constant-queue-push-left q (cons :b i))))))
		(mp:process-run-function "thread 3" ()
		  #'(lambda ()
		      (let ((ab::current-thread-index 3))
			(mp:semaphore-release r)
			(mp:semaphore-acquire w) ; wait for main thread
			(dotimes (i n)
			  (ab::constant-queue-push-left q (cons :c i))))))
		(mp:process-run-function "thread 4" ()
		  #'(lambda ()
		      (let ((ab::current-thread-index 4))
			(mp:semaphore-release r)
			(mp:semaphore-acquire w) ; wait for main thread
			(dotimes (i n)
			  (ab::constant-queue-push-left q (cons :d i)))))))))
    ;; 1. make sure threads are all ready
    (mp:semaphore-acquire r :count 4 :wait-reason "waiting for threads")
    ;; 2. let all threads start to enqueue data
    (dotimes (i (* 4 2)) ; doubled to make sure no threads wait
      (mp:semaphore-release w))
    ;; 3. wait for the finish of all threads
    (dolist (s schedulers) (mp:process-join s))
    ;; 4. dequeue all data and check
    (let (a b c d)
      (loop
        (multiple-value-bind (item ok)
	    (ab::constant-queue-pop-right q)
	  (cond (item
		 (case (car item)
		   (:a (push (cdr item) a))
		   (:b (push (cdr item) b))
		   (:c (push (cdr item) c))
		   (:d (push (cdr item) d))))
		(t
		 (return)))))
      (labels ((check-list (list)
		 (when list
		   (if (cdr list)
		       (when (= (first list) (1- (second list)))
			 (check-list (cdr list)))
		     (= (first list) (1- n))))))
	(assert-true (check-list (nreverse a)))
	(assert-true (check-list (nreverse b)))
	(assert-true (check-list (nreverse c)))
	(assert-true (check-list (nreverse d)))))))

;;; Test subject: single enqueue, parallel dequeue
;;; Used APIs:
;;;   AB::MAKE-EMPTY-CONSTANT-QUEUE
;;;   AB::CONSTANT-QUEUE-PUSH-LEFT
;;;   AB::CONSTANT-QUEUE-POP-RIGHT

#+(and SymScale LispWorks)
(define-test queue.tr.2
  (let ((q (ab::make-empty-constant-queue))
	(w (mp:make-semaphore :name "w" :count 0))
	(r (mp:make-semaphore :name "r" :count 0))
	(mbox (mp:make-mailbox :name "mbox" :size 4)))
    (dotimes (i 100000)
      (ab::constant-queue-push-left q i)) ; push-right
    (flet ((dq (i)
	     (mp:semaphore-release r)
	     (mp:semaphore-acquire w) ; wait for main thread
	     (let ((ab::current-thread-index i)
		   (last -1))
	       (loop
		 (multiple-value-bind (x ok)
		     (ab::constant-queue-pop-right q) ; pop-left
		   (cond (x
			  (if (> x last)
			      (setq last x)
			    (progn
			      (mp:mailbox-send mbox (list last x))
			      (return nil))))
			 (t
			  (mp:mailbox-send mbox t)
			  (return t))))))))
      (let ((deschedulers
	     (list (mp:process-run-function "thread 1" () #'dq 1)
		   (mp:process-run-function "thread 2" () #'dq 2)
		   (mp:process-run-function "thread 3" () #'dq 3)
		   (mp:process-run-function "thread 4" () #'dq 4))))
	(mp:semaphore-acquire r :count 4 :wait-reason "waiting for threads")
	(dotimes (i (* 4 2)) ; doubled to make sure no threads wait
	  (mp:semaphore-release w))
	(assert-equal (mapcar #'(lambda (th)
				  (mp:process-join th)
				  (mp:mailbox-read mbox))
			      deschedulers)
		      '(t t t t))))))

;;; Test subject: parallel enqueue, parallel dequeue
;;; Used APIs:
;;;   AB::MAKE-EMPTY-CONSTANT-QUEUE
;;;   AB::CONSTANT-QUEUE-PUSH-LEFT
;;;   AB::CONSTANT-QUEUE-POP-RIGHT

#+(and SymScale LispWorks)
(define-test queue.tr.3
  (let* ((q (ab::make-empty-constant-queue))
	 (w (mp:make-semaphore :name "w" :count 0))
	 (r (mp:make-semaphore :name "r" :count 0))
	 (n 100000)
	 (mbox (mp:make-mailbox :name "mbox" :size 4))
	 (schedulers
	  (list (mp:process-run-function "enqueue thread 1" ()
					 #'(lambda ()
					     (let ((ab::current-thread-index 1))
					       (mp:semaphore-release r)
					       (mp:semaphore-acquire w) ; wait for main thread
					       (dotimes (i n)
						 (ab::constant-queue-push-left q (cons :a i))))))
		(mp:process-run-function "enqueue thread 2" ()
					 #'(lambda ()
					     (let ((ab::current-thread-index 2))
					       (mp:semaphore-release r)
					       (mp:semaphore-acquire w) ; wait for main thread
					       (dotimes (i n)
						 (ab::constant-queue-push-left q (cons :b i))))))
		(mp:process-run-function "enqueue thread 3" ()
					 #'(lambda ()
					     (let ((ab::current-thread-index 3))
					       (mp:semaphore-release r)
					       (mp:semaphore-acquire w) ; wait for main thread
					       (dotimes (i n)
						 (ab::constant-queue-push-left q (cons :c i))))))
		(mp:process-run-function "enqueue thread 4" ()
					 #'(lambda ()
					     (let ((ab::current-thread-index 4))
					       (mp:semaphore-release r)
					       (mp:semaphore-acquire w) ; wait for main thread
					       (dotimes (i n)
						 (ab::constant-queue-push-left q (cons :d i)))))))))
    (flet ((dq (i)
	     (let ((ab::current-thread-index i)
		   (a -1) (ac 0)
		   (b -1) (bc 0)
		   (c -1) (cc 0)
		   (d -1) (dc 0))
	       (mp:semaphore-release r)
	       (mp:semaphore-acquire w) ; wait for main thread
	       (loop
		 (multiple-value-bind (item ok)
		     (ab::constant-queue-pop-right q)
		   (cond (item
			  (let ((m (cdr item)))
			    (macrolet ((test-on (name c)
					 `(if (< ,name m)
					      (progn
						(setq ,name m)
						(incf ,c))
					    (progn
					      (mp:mailbox-send mbox nil)
					      (return nil)))))
			      (ecase (car item)
				(:a (test-on a ac))
				(:b (test-on b bc))
				(:c (test-on c cc))
				(:d (test-on d dc))))))
			 (t
			  (mp:mailbox-send mbox (list a ac b bc c cc d dc))
			  (return t))))))))
      (let ((deschedulers
	     (list (mp:process-run-function "dequeue thread 1" () #'dq 5)
		   (mp:process-run-function "dequeue thread 2" () #'dq 6)
		   (mp:process-run-function "dequeue thread 3" () #'dq 7)
		   (mp:process-run-function "dequeue thread 4" () #'dq 8))))
	(mp:semaphore-acquire r :count 8 :wait-reason "waiting for threads")
	(dotimes (i (* 8 2)) ; doubled to make sure no threads wait
	  (mp:semaphore-release w))
	(let ((a -1) (ac 0)
	      (b -1) (bc 0)
	      (c -1) (cc 0)
	      (d -1) (dc 0))
	  (mapc #'(lambda (th)
		    (mp:process-join th)
		    (let ((results (mp:mailbox-read mbox)))
		      (when results
			(destructuring-bind (ta tac tb tbc tc tcc td tdc) results
			  (setf a (max ta a)
				b (max tb b)
				c (max tc c)
				d (max td d))
			  (incf ac tac)
			  (incf bc tbc)
			  (incf cc tcc)
			  (incf dc tdc)))))
		deschedulers)
	  (assert-true (and (= n ac (1+ a))
			    (= n bc (1+ b))
			    (= n cc (1+ c))
			    (= n dc (1+ d)))))))))
