(in-package :ab)

(defvar enqueue-future-task-finished nil)
(defvar dequeue-future-task-finished nil)
(defvar task nil)

(defun make-task-with-priority (priority)
        (progn
             (setf task                                        (make-schedule-task-macro nil))
             (setf (schedule-task-time                         task) 0.0d0)
             (setf (schedule-task-cycle-interval               task) 0.0d0)
             (setf (schedule-task-g2-running-p                 task) nil)
             (setf (schedule-task-priority                     task) priority)
             (setf (schedule-task-ensure-cycle-anniversaries-p task) nil)
             (setf (schedule-task-argument-reclaimers          task) nil)
             (setf (schedule-task-thread                       task) nil)
             (setf (schedule-task-function-name                task) nil)
             (setf (schedule-task-function                     task) nil)
             (setf (schedule-task-argument-count               task) nil)
             (setf (schedule-task-arg-1                        task) nil)
             (setf (schedule-task-arg-2                        task) nil)
             (setf (schedule-task-arg-3                        task) nil)
             (setf (schedule-task-arg-4                        task) nil)))

(defun lockfree-queue-mt-ab-future-task-test()
  (initialize-scheduler)
  (make-task-with-priority 1)
  (loop for entries from 1 below 2 do 
        (setup-enqueue-future-task))
  (loop for entries from 1 below 2 do 
        (setup-dequeue-future-task))
  (setup-tester-mt-queue-future-task))

(defun setup-enqueue-future-task() 
        (push (list "enqueue-thread" ()
                        (lambda ()
                          (loop for entries from 1 below 2 do 
                                (get-or-create-future-task-queue-for-task task))))
                        mp:*initial-processes*)

        (setq enqueue-future-task-finished t))
                  
(defun setup-dequeue-future-task()
        (push (list "dequeue-thread" ()
                        (lambda ()
                          (loop for entries from 1 below 2 do 
                                (delete-future-task-queue-for-task task))))
                        mp:*initial-processes*)
        (setq dequeue-future-task-finished t))
                  
(defun setup-tester-mt-queue-future-task()
        (push (list "tester-thread" nil 'test-queue-dequeue-future-task)
                  mp:*initial-processes*))
                  
(defun-void test-queue-dequeue-future-task() 
  (sleep 30) ; let the enqueue and dequeue threads finish their job
  (mp:process-wait "waiting for threads to complete"
		   (lambda ()
		     (and enqueue-future-task-finished dequeue-future-task-finished)))
  (lisp-unit:assert-false (future-tasks-exist-p future-g2-time-tasks)))

(in-package :tests)

(defun lockfree-skiplist-priority-queue-mt-test()
  (ab::lockfree-queue-mt-ab-future-task-test))

(define-test test-z-lockfree-skiplist-priority-queue-mt
  (lockfree-skiplist-priority-queue-mt-test)
  (format t "test lockfree-skiplist-priority-queue-mt-test SUCCESS~%")
  (assert-true t))
