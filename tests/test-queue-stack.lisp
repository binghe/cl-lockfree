(in-package :tests)

;;; Test subject: queue as stack, parallel push left, parallel pop left
;;;
;;; Used APIs:
;;;   AB::MAKE-EMPTY-CONSTANT-QUEUE
;;;   AB::CONSTANT-QUEUE-PUSH-LEFT (filo-enqueue)
;;;   AB::CONSTANT-QUEUE-POP-LEFT (dequeue)

#+(and SymScale LispWorks)
(define-test queue.stack.left
  (let* ((q (ab::make-empty-constant-queue))
	 (w (mp:make-semaphore :name "w" :count 0))
	 (r (mp:make-semaphore :name "r" :count 0))
	 (mbox (mp:make-mailbox :name "mbox" :size 4))
	 (n 100000)
	 (schedulers
	  (list (mp:process-run-function "thread 1 (push-left)" ()
		  #'(lambda ()
		      (let ((ab::current-thread-index 1))
			(mp:semaphore-release r)
			(mp:semaphore-acquire w) ; wait for main thread
			(dotimes (i n)
			  (ab::constant-queue-push-left q (cons :a i))))))
		(mp:process-run-function "thread 2 (push-left)" ()
		  #'(lambda ()
		      (let ((ab::current-thread-index 2))
			(mp:semaphore-release r)
			(mp:semaphore-acquire w) ; wait for main thread
			(dotimes (i n)
			  (ab::constant-queue-push-left q (cons :b i))))))
		(mp:process-run-function "thread 3 (push-left)" ()
		  #'(lambda ()
		      (let ((ab::current-thread-index 3))
			(mp:semaphore-release r)
			(mp:semaphore-acquire w) ; wait for main thread
			(dotimes (i n)
			  (ab::constant-queue-push-left q (cons :c i))))))
		(mp:process-run-function "thread 4 (push-left)" ()
		  #'(lambda ()
		      (let ((ab::current-thread-index 4))
			(mp:semaphore-release r)
			(mp:semaphore-acquire w) ; wait for main thread
			(dotimes (i n)
			  (ab::constant-queue-push-left q (cons :d i)))))))))
    (flet ((dq (i)
	     (let ((ab::current-thread-index i)
		   (ac 0)
		   (bc 0)
		   (cc 0)
		   (dc 0))
	       (mp:semaphore-release r)
	       (mp:semaphore-acquire w) ; wait for main thread
	       (loop with set = nil
		     do
		 (multiple-value-bind (item ok)
		     (ab::constant-queue-pop-left q)
		   (cond (item
			  (let ((m (cdr item)))
			    (ecase (car item)
			      (:a (incf ac))
			      (:b (incf bc))
			      (:c (incf cc))
			      (:d (incf dc)))))
			 (t
			  (unless (some #'mp:process-alive-p schedulers)
			    (mp:mailbox-send mbox (list ac bc cc dc))
			    (return t)))))))))
      (let ((deschedulers
	     (list (mp:process-run-function "thread 5 (pop-left)" () #'dq 5)
		   (mp:process-run-function "thread 6 (pop-left)" () #'dq 6)
		   (mp:process-run-function "thread 7 (pop-left)" () #'dq 7)
		   (mp:process-run-function "thread 8 (pop-left)" () #'dq 8))))
	(mp:semaphore-acquire r :count 2 :wait-reason "waiting for threads")
	(dotimes (i (* 8 2)) ; doubled to make sure no threads wait
	  (mp:semaphore-release w))	
	(let ((ac 0)
	      (bc 0)
	      (cc 0)
	      (dc 0))
	  (mapc #'(lambda (th)
		    (mp:process-join th)
		    (let ((results (mp:mailbox-read mbox)))
		      (when results
			(destructuring-bind (tac tbc tcc tdc) results
			  (incf ac tac)
			  (incf bc tbc)
			  (incf cc tcc)
			  (incf dc tdc)))))
		deschedulers)
	  (assert-true (and (= n ac) (= n bc) (= n cc) (= n dc))))))))

;;; Test subject: queue as stack, parallel push right, parallel pop right
;;;
;;; Used APIs:
;;;   AB::MAKE-EMPTY-CONSTANT-QUEUE
;;;   AB::CONSTANT-QUEUE-PUSH-RIGHT (enqueue)
;;;   AB::CONSTANT-QUEUE-POP-RIGHT (filo-dequeue)

#+(and SymScale LispWorks)
(define-test queue.stack.right
  (let* ((q (ab::make-empty-constant-queue))
	 (w (mp:make-semaphore :name "w" :count 0))
	 (r (mp:make-semaphore :name "r" :count 0))
	 (mbox (mp:make-mailbox :name "mbox" :size 4))
	 (n 100000)
	 (schedulers
	  (list (mp:process-run-function "thread 1 (push-right)" ()
		  #'(lambda ()
		      (let ((ab::current-thread-index 1))
			(mp:semaphore-release r)
			(mp:semaphore-acquire w) ; wait for main thread
			(dotimes (i n)
			  (ab::constant-queue-push-right q (cons :a i))))))
		(mp:process-run-function "thread 2 (push-right)" ()
		  #'(lambda ()
		      (let ((ab::current-thread-index 2))
			(mp:semaphore-release r)
			(mp:semaphore-acquire w) ; wait for main thread
			(dotimes (i n)
			  (ab::constant-queue-push-right q (cons :b i))))))
		(mp:process-run-function "thread 3 (push-right)" ()
		  #'(lambda ()
		      (let ((ab::current-thread-index 3))
			(mp:semaphore-release r)
			(mp:semaphore-acquire w) ; wait for main thread
			(dotimes (i n)
			  (ab::constant-queue-push-right q (cons :c i))))))
		(mp:process-run-function "thread 4 (push-right)" ()
		  #'(lambda ()
		      (let ((ab::current-thread-index 4))
			(mp:semaphore-release r)
			(mp:semaphore-acquire w) ; wait for main thread
			(dotimes (i n)
			  (ab::constant-queue-push-right q (cons :d i)))))))))
    (flet ((dq (i)
	     (let ((ab::current-thread-index i)
		   (ac 0)
		   (bc 0)
		   (cc 0)
		   (dc 0))
	       (mp:semaphore-release r)
	       (mp:semaphore-acquire w) ; wait for main thread
	       (loop with set = nil
		     do
		 (multiple-value-bind (item ok)
		     (ab::constant-queue-pop-right q)
		   (cond (item
			  (let ((m (cdr item)))
			    (ecase (car item)
			      (:a (incf ac))
			      (:b (incf bc))
			      (:c (incf cc))
			      (:d (incf dc)))))
			 (t
			  (unless (some #'mp:process-alive-p schedulers)
			    (mp:mailbox-send mbox (list ac bc cc dc))
			    (return t)))))))))
      (let ((deschedulers
	     (list (mp:process-run-function "thread 5 (pop-right)" () #'dq 5)
		   (mp:process-run-function "thread 6 (pop-right)" () #'dq 6)
		   (mp:process-run-function "thread 7 (pop-right)" () #'dq 7)
		   (mp:process-run-function "thread 8 (pop-right)" () #'dq 8))))
	(mp:semaphore-acquire r :count 2 :wait-reason "waiting for threads")
	(dotimes (i (* 8 2)) ; doubled to make sure no threads wait
	  (mp:semaphore-release w))	
	(let ((ac 0)
	      (bc 0)
	      (cc 0)
	      (dc 0))
	  (mapc #'(lambda (th)
		    (mp:process-join th)
		    (let ((results (mp:mailbox-read mbox)))
		      (when results
			(destructuring-bind (tac tbc tcc tdc) results
			  (incf ac tac)
			  (incf bc tbc)
			  (incf cc tcc)
			  (incf dc tdc)))))
		deschedulers)
	  (assert-true (and (= n ac) (= n bc) (= n cc) (= n dc))))))))
