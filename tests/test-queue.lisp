;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was written at
;;;; Carnegie Mellon University and released into the public domain. The
;;;; software is in the public domain and is provided with absolutely no
;;;; warranty. See the COPYING and CREDITS files for more information.

;;; (run-tests '(queue.1 queue.2 queue.3 queue.4 queue.5 queue.6 queue.7))
;;; (run-tests '(queue.t.1 queue.t.2 queue.t.3))

(in-package :tests)

(define-test queue.1
  (let ((q (ab::make-empty-constant-queue)))
    (ab::constant-queue-enqueue q 1)
    (ab::constant-queue-enqueue q 2)
    (ab::constant-queue-enqueue q 3)
    (ab::constant-queue-enqueue q 4)
    (assert-equal (ab::constant-queue-dequeue q) (values 1 t))
    (prog1
	(assert-equal (ab::loop for e being each ab::constant-queue-element of q
				collect e)
		      '(2 3 4))
      (ab::reclaim-constant-queue q))))

(defun constant-queue-dequeue (q)
  (ab::constant-queue-dequeue q))

(define-test queue.2
  (assert-false (constant-queue-dequeue
		  (ab::make-empty-constant-queue))))

(define-test queue.3
  (let ((q (ab::make-empty-constant-queue)))
    (ab::constant-queue-enqueue q nil)
    (assert-false (constant-queue-dequeue q))))

;; GENSYMCID-1780
#-exclude-possible-bugs
(define-test queue.4
  (let ((q (ab::make-empty-constant-queue)))
    (prog1 (assert-true (ab::constant-queue-p q))
      (ab::reclaim-constant-queue q))))

(defun constant-queue-empty-p (q)
  (ab::constant-queue-empty-p q))

(define-test queue.5
  (let ((q (ab::make-empty-constant-queue)))
    (ab::constant-queue-enqueue q 1)
    (ab::constant-queue-enqueue q 2)
    (ab::constant-queue-enqueue q 3)
    (ab::constant-queue-enqueue q 4)
    (ab::constant-queue-enqueue q 5)
    (assert-equal 5 (ab::constant-queue-length q))
    (assert-eq (ab::queue-datum (ab::constant-queue-enqueue q 'foo))
	       'foo)
    (assert-equal 6 (ab::constant-queue-length q))
    (assert-equal (values 1 t) (constant-queue-dequeue q))
    (assert-equal 5 (ab::constant-queue-length q))
    (assert-equal (values 2 t) (constant-queue-dequeue q))
    (assert-equal 4 (ab::constant-queue-length q))
    (assert-equal (values 3 t) (constant-queue-dequeue q))
    (assert-equal 3 (ab::constant-queue-length q))
    (assert-equal (values 4 t) (constant-queue-dequeue q))
    (assert-equal 2 (ab::constant-queue-length q))
    (assert-equal (values 5 t) (constant-queue-dequeue q))
    (assert-equal 1 (ab::constant-queue-length q))
    (assert-true (not (constant-queue-empty-p q)))
    (assert-equal (constant-queue-dequeue q) (values 'foo t))
    (assert-equal 0 (ab::constant-queue-length q))
    (assert-true (constant-queue-empty-p q))
    (assert-false (constant-queue-dequeue q))
    (assert-equal 0 (ab::constant-queue-length q))
    (prog1 (assert-true (constant-queue-empty-p q))
      (ab::reclaim-constant-queue q))))

;;; Single-threaded deletion test
;;; Used APIs:
;;;   AB::CONSTANT-QUEUE-DELETE
;;;   AB::CONSTANT-QUEUE-PREVIOUS
;;;   AB::CONSTANT-QUEUE-NEXT

(define-test queue.6
  (let ((q (ab::make-empty-constant-queue)))
    (ab::constant-queue-enqueue q 1)
    (ab::constant-queue-enqueue q 2)
    (ab::constant-queue-enqueue q 3)
    (ab::constant-queue-enqueue q 4)
    (ab::constant-queue-enqueue q 5)
    (let* ((head (ab::constant-queue-head q))
	   (tail (ab::constant-queue-tail q))
	   (first #+Lockfree-Deque (ab::constant-queue-next head q)
		  #-Lockfree-Deque head)
	   (last #+Lockfree-Deque (ab::constant-queue-previous tail q)
		 #-Lockfree-Deque tail))
      (assert-equal (ab::constant-queue-delete first q) (values 1 t))
      (assert-equal 4 (ab::constant-queue-length q))
      (assert-equal (ab::constant-queue-delete last q) (values 5 t))
      (prog1 (assert-equal 3 (ab::constant-queue-length q))
	(ab::reclaim-constant-queue q)))))

;;; Single-threaded insert-before/after test
;;; Used APIs:
;;;   AB::CONSTANT-QUEUE-INSERT-BEFORE
;;;   AB::CONSTANT-QUEUE-INSERT-AFTER
;;;   AB::CONSTANT-QUEUE-LENGTH

(define-test queue.7
  (let ((q (ab::make-empty-constant-queue)))
    (ab::constant-queue-enqueue q 0)
    (let* ((head (ab::constant-queue-head q))
	   (middle #+Lockfree-Deque (ab::constant-queue-next head q)
		   #-Lockfree-Deque head))
      (assert-equal (ab::constant-queue-read middle) 0)
      ;; after the middle node, we're going to insert 10000 node on the left,
      ;; same on the right.
      (loop for i from -1000 to -1 do
	(ab::constant-queue-insert-before q middle i))
      (loop for i from 1000 downto 1 do
	(ab::constant-queue-insert-after q middle i))
      (prog1
	  (assert-equal (ab::constant-queue-length q) 2001)
	(ab::reclaim-constant-queue q)))))

;;; Test subject: parallel enqueue, single dequeue
;;; Used APIs:
;;;   AB::MAKE-EMPTY-CONSTANT-QUEUE
;;;   AB::CONSTANT-QUEUE-ENQUEUE (PushRight)
;;;   AB::CONSTANT-QUEUE-DEQUEUE (PopLeft)

#+(and SymScale LispWorks)
(define-test queue.t.1 ; parallel enqueue, single dequeue
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
			  (ab::constant-queue-enqueue q (cons :a i))))))
		(mp:process-run-function "thread 2" ()
		  #'(lambda ()
		      (let ((ab::current-thread-index 2))
			(mp:semaphore-release r)
			(mp:semaphore-acquire w) ; wait for main thread
			(dotimes (i n)
			  (ab::constant-queue-enqueue q (cons :b i))))))
		(mp:process-run-function "thread 3" ()
		  #'(lambda ()
		      (let ((ab::current-thread-index 3))
			(mp:semaphore-release r)
			(mp:semaphore-acquire w) ; wait for main thread
			(dotimes (i n)
			  (ab::constant-queue-enqueue q (cons :c i))))))
		(mp:process-run-function "thread 4" ()
		  #'(lambda ()
		      (let ((ab::current-thread-index 4))
			(mp:semaphore-release r)
			(mp:semaphore-acquire w) ; wait for main thread
			(dotimes (i n)
			  (ab::constant-queue-enqueue q (cons :d i)))))))))
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
	    (ab::constant-queue-dequeue q)
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
;;;   AB::CONSTANT-QUEUE-ENQUEUE
;;;   AB::CONSTANT-QUEUE-DEQUEUE

#+(and SymScale LispWorks)
(define-test queue.t.2
  (let ((q (ab::make-empty-constant-queue))
	(w (mp:make-semaphore :name "w" :count 0))
	(r (mp:make-semaphore :name "r" :count 0))
	(mbox (mp:make-mailbox :name "mbox" :size 4)))
    (dotimes (i 100000)
      (ab::constant-queue-enqueue q i)) ; push-right
    (flet ((dq (i)
	     (mp:semaphore-release r)
	     (mp:semaphore-acquire w) ; wait for main thread
	     (let ((ab::current-thread-index i)
		   (last -1))
	       (loop
		 (multiple-value-bind (x ok)
		     (ab::constant-queue-dequeue q) ; pop-left
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
;;;   AB::CONSTANT-QUEUE-ENQUEUE
;;;   AB::CONSTANT-QUEUE-DEQUEUE

#+(and SymScale LispWorks)
(define-test queue.t.3
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
						 (ab::constant-queue-enqueue q (cons :a i))))))
		(mp:process-run-function "enqueue thread 2" ()
					 #'(lambda ()
					     (let ((ab::current-thread-index 2))
					       (mp:semaphore-release r)
					       (mp:semaphore-acquire w) ; wait for main thread
					       (dotimes (i n)
						 (ab::constant-queue-enqueue q (cons :b i))))))
		(mp:process-run-function "enqueue thread 3" ()
					 #'(lambda ()
					     (let ((ab::current-thread-index 3))
					       (mp:semaphore-release r)
					       (mp:semaphore-acquire w) ; wait for main thread
					       (dotimes (i n)
						 (ab::constant-queue-enqueue q (cons :c i))))))
		(mp:process-run-function "enqueue thread 4" ()
					 #'(lambda ()
					     (let ((ab::current-thread-index 4))
					       (mp:semaphore-release r)
					       (mp:semaphore-acquire w) ; wait for main thread
					       (dotimes (i n)
						 (ab::constant-queue-enqueue q (cons :d i)))))))))
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
		     (ab::constant-queue-dequeue q)
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
			  (unless (some #'mp:process-alive-p schedulers)
			    (mp:mailbox-send mbox (list a ac b bc c cc d dc))
			    (return t)))))))))
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
