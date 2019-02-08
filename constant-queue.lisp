;;;; Queues With Constant Insert, Dequeue, and Delete Operations

(in-package :lockfree)

;;; The following forms implement a type of queue which has constant time
;;; insert, dequeue, and delete operations.

;;; The lock-free verion is based on algorithms from following papers:
;;;
;;; Sundell, Håkan. Efficient and practical non-blocking data structures.
;;; Department of Computer Engineering, Chalmers University of Technology, 2004.

;;; The structure `queue-element' is used to represent the elements of constant
;;; queues.  They have next-element, previous-element, and datum slots.  Note
;;; that these structures are declared to explicitly be of type vector, so as to
;;; eliminate the name and save a word of memory per instance.  Note that this
;;; means there is no predicate for this structure.

(def-structure (queue-element
                 (:type vector)
                 (:constructor make-queue-element
                  (queue-next-element queue-previous-element queue-datum))
                 ;; (:eliminate-for-products gsi)
                 )
  #+Lockfree-Deque
  (reserved-slot-for-chaining nil)
  #+Lockfree-Deque		    ; this cannot be the first slot which is also
  (reference-count-and-claim-bit 1) ; used for chaining
  ;; fix the literal number in `constant-queue-p' if more slots were added
  queue-next-element		; also head
  queue-previous-element	; also tail
  queue-datum)			; also mark

(defmacro reference-count (queue-element)
  `(ash (reference-count-and-claim-bit ,queue-element) -1))

(defmacro claim-bit (queue-element)
  `(ldb (byte 1 0) (reference-count-and-claim-bit ,queue-element)))

(defconstant constant-queue-marker '(constant-queue-marker))

(def-substitution-macro constant-queue-p (thing)
  (and (simple-vector-p thing)
       (=f (length (the simple-vector thing))
	   #-Lockfree-Deque 3
	   #+Lockfree-Deque 5)
       (eq (queue-datum thing) constant-queue-marker)))

#+Lockfree-Deque
(defmacro safe-queue-read (place)
  (let ((q (gensym)))
    `(loop for ,q = ,place do
       (unless ,q (return nil))
       (atomic-incf (reference-count-and-claim-bit ,place) 2)
       (if (eq ,q ,place)
	   (return ,q)
	 (release-queue-node ,q)))))

#+Lockfree-Deque
(defmacro copy-queue-node (node-or-place) ; COPY_NODE
  `(safe-queue-read ,node-or-place))

#+Lockfree-Deque
(defun-simple read-queue-node (reference) ; READ_NODE
  (multiple-value-bind (node mark)
      (get-atomic-reference reference)
    (unless mark
      (safe-queue-read node))))

#+Lockfree-Deque ; READ_DEL_NODE
(defun-substitution-macro read-deleted-queue-node (reference)
  (let ((node (get-atomic-reference reference)))
    (safe-queue-read node)
    node))

#+Lockfree-Deque
(defun-simple create-queue-element (thing)
  (let ((node (make-queue-element-macro nil nil nil)))			  ; C1
    (setq node (safe-queue-read node))
    (clear-lowest-bit (reference-count-and-claim-bit node))
    (setf (queue-datum node) thing)					  ; C2
    node))								  ; C3

(defun release-queue-node (node)
  (when (null node)
    (return-from release-queue-node))
  #+Lockfree-Deque
  (when (=f 0 (decrement-and-test-and-set (reference-count-and-claim-bit node)))
    (return-from release-queue-node))
  #+Lockfree-Deque
  (release-reference node)
  (reclaim-queue-element-macro node))

;;; The function `make-empty-constant-queue' returns a new, empty constant
;;; queue.  Constant queues are represented with a queue-element, where the head
;;; of the queue is stored in the next-element slot, the tail of the queue is
;;; stored in the previous-element slot, and the datum slot contains the
;;; constant-queue-head marker.  Empty constant queues contain pointers back to
;;; the queue element in the head and tail slots.

#+Lockfree-Deque
(defconstant constant-queue-head-marker '(constant-queue-head-marker))
#+Lockfree-Deque
(defconstant constant-queue-tail-marker '(constant-queue-tail-marker))

(defmacro queue-next-element-real (queue-element)
  `(atomic-reference-object
     (queue-next-element ,queue-element)))

(defmacro queue-previous-element-real (queue-element)
  `(atomic-reference-object
     (queue-previous-element ,queue-element)))

#+Lockfree-Deque
(defun release-reference (node)
  (release-queue-node (queue-previous-element-real node))		  ; RR1
  (release-queue-node (queue-next-element-real node)))			  ; RR2

(defmacro constant-queue-head (constant-queue)
  `(queue-next-element ,constant-queue))

(defmacro constant-queue-tail (constant-queue)
  `(queue-previous-element ,constant-queue))

(def-substitution-macro constant-queue-head-if (constant-queue)
  (when constant-queue
    (constant-queue-head constant-queue)))

(def-substitution-macro constant-queue-tail-if (constant-queue)
  (when constant-queue
    (constant-queue-tail constant-queue)))

#-Lockfree-Deque
(defun-simple make-empty-constant-queue ()
  (let ((new-queue (make-queue-element-macro
                     nil nil constant-queue-marker)))
    (setf (constant-queue-head new-queue) new-queue)
    (setf (constant-queue-tail new-queue) new-queue)
    new-queue))

#+Lockfree-Deque
(defun-simple make-empty-constant-queue ()
  (let ((new-queue (make-queue-element-macro
		     nil nil constant-queue-marker))
	(head (make-queue-element-macro
		nil (make-atomic-reference nil) constant-queue-head-marker))
	(tail (make-queue-element-macro
		(make-atomic-reference nil) nil constant-queue-tail-marker)))
    (setq head (safe-queue-read head)
	  tail (safe-queue-read tail))
    (clear-lowest-bit (reference-count-and-claim-bit head))
    (clear-lowest-bit (reference-count-and-claim-bit tail))
    (setf (queue-next-element head) (make-atomic-reference tail))
    (setf (queue-previous-element tail) (make-atomic-reference head))
    (setf (constant-queue-head new-queue) head)
    (setf (constant-queue-tail new-queue) tail)
    new-queue))

;;; The `Next' function tries to change the cursor to the next position
;;; relative to the current position, and returns the status of success. The
;;; algorithm repeatedly in line NT2-NT11 checks the next node for possible
;;; traversal until the found node is present and is not the tail dummy node.
;;; If the current node is the tail dummy node, false is returned in line NT2.
;;; In line NT3 the next pointer of the current node is de-referenced and in
;;; line NT4 the deletion state of the found node is read. If the found node
;;; is deleted and the current node was deleted when directly next of the
;;; found node, this is detected in line NT5 and then the position is updated
;;; according to [Def 1]* in line NT10. If the found node was detected as
;;; present in line NT5, the cursor is set to the found node in line NT10 and
;;; true is returned (unless the found node is the tail dummy node when
;;; instead false is returned) in line NT11. Otherwise it's checked if the
;;; found node is not already fully deleted in line NT6 and then fulfils the
;;; deletion by calling the HelpDelete procedure after which the algorithm
;;; retries at line NT2. The linearizability point of a Next function that
;;; succeeds is the read sub-operation of the next pointer in line NT3. The
;;; linearizability point of cursor was the tail dummy node, and the read sub-
;;; operation of the next pointer in line NT3 otherwise.

;;; [Def 1] The position of a cursor that references a node that is present in
;;; the list is the referenced node. The position of a cursor that references
;;; a deleted node, is represented by the node that was logically next of the
;;; deleted node at the very moment of the deletion (i.e. the setting of the
;;; deletion mark). If that node is deleted as well, the position is equal to
;;; the position of a cursor referencing that node, and so on recursively. The
;;; actual position is then interpreted to be at an imaginary node directly
;;; previous of the representing node.

#-Lockfree-Deque
(defmacro constant-queue-next (cursor constant-queue)
  (declare (ignore constant-queue))
  `(queue-next-element ,cursor))

#+(or Lockfree-Deque Lockfree-List)
(defmacro generate-*-next ((cursor container)
			   tail-element
			   next-element
			   read-deleted-node
			   release-node
			   help-delete)
  `(progn
     (loop with tail = (,tail-element ,container)			  ; NT1
	   do
       (when (eq ,cursor tail) (return nil))				  ; NT2
       (let* ((next (,read-deleted-node (,next-element ,cursor)))	  ; NT3
	      (d (atomic-reference-mark (,next-element next))))		  ; NT4
	 (cond ((and d
		     (atomic-reference-neq
		       (,next-element ,cursor)
		       (make-atomic-reference next t)))			  ; NT5
		(when (eq next (atomic-reference-object
				 (,next-element ,cursor)))
		  (,help-delete next))					  ; NT6
		(,release-node next))					  ; NT7
	       (t
		(,release-node next) ; old: cursor			  ; NT9
		(setq ,cursor next)					  ; NT10
		(when (and (not d)
			   (neq next tail))
		  (return ,cursor))))))))				  ; NT11

#+Lockfree-Deque
(defun-simple constant-queue-next (cursor constant-queue)
  (generate-*-next (cursor constant-queue)
    constant-queue-tail
    queue-next-element
    read-deleted-queue-node
    release-queue-node
    help-delete-queue-node))

;;; The `Prev' function tries to change the cursor to the previous position
;;; relative to the current position, and returns the status of success. The
;;; algorithm repeatedly in line PV2-PV11 checks the next node for possible
;;; traversal until the found node is present and is not the head dummy node.
;;; If the current node is the head dummy node, false is returned in line PV2.
;;; In line PV3 the prev pointer of the current node is de-referenced. If the
;;; found node is directly previous of the current node and the current node
;;; is present, this is detected in line PV4 and then the cursor is set to the
;;; found node in line PV6 and true is returned (unless the found node is the
;;; head dummy node when instead false is returned) in line PV7. If the current
;;; node is deleted then the cursor position is updated according to [Def 1]*
;;; by calling the `Next' function in line PV8. Otherwise the prev pointer of
;;; the current node is updated by calling the `HelpInsert' function in line
;;; PV10 after which the algorithm retries at line PV2. The linearizability
;;; point of a Prev function that succeeds is the read sub-operation of the prev
;;; pointer in line PV13. The linearizability point of a Prev function that
;;; fails is line PV2 if the node positioned by the original cursor was the head
;;; dummy node, and the read sub-operation of the prev pointer in line PV3
;;; otherwise.

#-Lockfree-Deque
(defmacro constant-queue-previous (cursor constant-queue)
  (declare (ignore constant-queue))
  `(queue-previous-element ,cursor))

#+(or Lockfree-Deque Lockfree-List)
(defmacro generate-*-previous ((cursor structure)
			       head-element
			       next-element
			       previous-element
			       read-deleted-node
			       release-node
			       help-insert
			       structure-next)
  `(progn
     (loop with head = (,head-element ,structure)			  ; PV1
	   do
       (when (eq ,cursor head) (return nil))				  ; PV2
       (let ((prev (,read-deleted-node
		     (,previous-element ,cursor))))			  ; PV3
	 (cond ((and (atomic-reference-equal
		       (,next-element prev)
		       (make-atomic-reference ,cursor nil))
		     (not (atomic-reference-mark
			    (,next-element ,cursor))))			  ; PV4
		(,release-node prev) ; old: cursor			  ; PV5
		(setq ,cursor prev)					  ; PV6
		(when (neq prev head) (return ,cursor)))		  ; PV7
	       ((atomic-reference-mark (,next-element ,cursor))
		(setq ,cursor
		      (,structure-next ,cursor ,structure)))		  ; PV8
	       (t							  ; PV9
		(setq prev (,help-insert prev ,cursor))			  ; PV10
		(,release-node prev)))))))				  ; PV11

#+Lockfree-Deque
(defun constant-queue-previous (cursor constant-queue)
  (generate-*-previous (cursor constant-queue)
    constant-queue-head
    queue-next-element
    queue-previous-element
    read-deleted-queue-node
    release-queue-node
    help-insert-queue-node
    constant-queue-next))

;;; The `Read' function returns the current value of the node referenced by
;;; the cursor, unless this node is deleted or the node is equal to any of
;;; the dummy nodes when the function instead returns a non-value. In line
;;; RD1 the algorithm checks if the node referenced by the cursor is either
;;; the head or tail dummy node, and then returns a non-value. The value of
;;; the node is read in line RD2, and in line RD3 it is checked if the node
;;; is deleted and then returns a non-value, otherwise the value is returned
;;; in line RD4. The linearizability point of a Read function that returns
;;; a value is the read sub-operation of the next pointer in line RD3. The
;;; linearizability point of a Read function that returns a non-value is the
;;; read sub-operation of the next pointer in line RD3, unless the node
;;; positioned by the cursor was the head or tail dummy node when the
;;; linearizability point is line RD1.

#+Lockfree-Deque
(defun constant-queue-read (cursor &optional constant-queue)
  (if (or (eq cursor (constant-queue-head-if constant-queue))		  ; RD1
	  (eq cursor (constant-queue-tail-if constant-queue)))
      nil
    (let ((value (queue-datum cursor)))					  ; RD2
      (if (atomic-reference-mark (queue-next-element cursor))		  ; RD3
	  nil
	value))))							  ; RD4

#-Lockfree-Deque
(defun constant-queue-read (cursor &optional constant-queue)
  (declare (ignore constant-queue))
  (let ((value (queue-datum cursor)))
    value))

#-Lockfree-Deque
(defun-simple clear-constant-queue (constant-queue)
  (declare (eliminate-for-gsi))
  (loop for element = (constant-queue-head constant-queue)
                    then (prog1 (queue-next-element element)
                                (reclaim-queue-element-macro element))
        until (eq element constant-queue))
  (setf (constant-queue-head constant-queue) constant-queue)
  (setf (constant-queue-tail constant-queue) constant-queue)
  constant-queue)

#+Lockfree-Deque
(defun-simple clear-constant-queue (constant-queue)
  (declare (eliminate-for-gsi))
  (let ((head (constant-queue-head constant-queue))
        (tail (constant-queue-tail constant-queue)))
    (loop with next-element-structure = nil
	  for element-structure = (queue-next-element-real head)
	                        then next-element-structure
	  until (eq element-structure tail)
	  do
      (setf next-element-structure (queue-next-element-real element-structure))
      (reclaim-queue-element-macro element-structure))
    (setf (queue-next-element head)
          (make-atomic-reference tail))
    (setf (queue-previous-element tail)
          (make-atomic-reference head))
    constant-queue))

#-Lockfree-Deque
(defun-simple reclaim-constant-queue (constant-queue)
  (loop for element = (constant-queue-head constant-queue)
                    then (prog1 (queue-next-element element)
                                #+development
                                (setf (queue-next-element element) nil)
                                (reclaim-queue-element-macro element))
        until (eq element constant-queue))
  (setf (queue-datum constant-queue) nil)
  (reclaim-queue-element-macro constant-queue)
  nil)

#+Lockfree-Deque
(defun-simple reclaim-constant-queue (constant-queue)
  (let ((head (constant-queue-head constant-queue))
        (tail (constant-queue-tail constant-queue)))
    (loop for element = head
                   then (prog1 (queue-next-element-real element)
                          (reclaim-queue-element-macro element))
          until (eq element tail)
          finally (reclaim-queue-element-macro element)))
  (setf (queue-datum constant-queue) nil)
  (reclaim-queue-element-macro constant-queue)
  nil)

#+development
(def-development-printer print-constant-queue (queue stream)
  (when (constant-queue-p queue)
    (printing-random-object (queue stream)
      (format stream "CONSTANT-QUEUE"))
    queue))

;;; The macro `constant-queue-peek' takes a constant queue and returns the
;;; next item to be dequeued.

#-Lockfree-Deque
(defmacro constant-queue-peek (constant-queue &optional (default-value nil))
  (let ((queue-var (if (symbolp constant-queue) constant-queue (gensym)))
        (first-entry (gensym)))
    `(let* (,@(if (neq queue-var constant-queue)
                  `((,queue-var ,constant-queue)))
            (,first-entry (constant-queue-head ,queue-var)))
       (if (neq ,first-entry ,queue-var)
           (queue-datum ,first-entry)
         ,default-value))))

#+Lockfree-Deque
(defmacro constant-queue-peek (constant-queue &optional (default-value nil))
  (let ((queue-var (if (symbolp constant-queue)
		       constant-queue
		     (make-symbol "QUEUE")))
	(head (make-symbol "HEAD"))
	(first (make-symbol "FIRST")))
    `(let* (,@(if (neq queue-var constant-queue)
		  `((,queue-var ,constant-queue)))
	    (,head (constant-queue-head ,queue-var))
	    (,first (constant-queue-next ,head ,queue-var)))
       (if ,first
	   (constant-queue-read ,first ,queue-var)
	 ,default-value))))

;;; The substitution macro `constant-queue-empty-p' returns whether or not the
;;; queue is empty.  If you want the datum of the first queue entry, call
;;; constant-queue-peek.

(def-substitution-macro constant-queue-empty-p (constant-queue)
  #-Lockfree-Deque
  (eq (constant-queue-head constant-queue) constant-queue)
  #+Lockfree-Deque
  (null (constant-queue-next
	  (constant-queue-head constant-queue) constant-queue)))

(def-substitution-macro constant-queue-non-empty-p (constant-queue)
  (not (constant-queue-empty-p constant-queue)))

;;; The macro `constant-queue-enqueue' takes a constant queue and a thing to
;;; be enqueued, and enqueues that item in the queue for FIFO dequeuing.  This
;;; function returns the new entry for the given thing in the queue.

;;; Since the head and tail pointers of an empty queue point back to the queue
;;; itself, we do not need to check for the empty queue in this enqueuing
;;; operation.  This is true since setting the "next-element" of the "tail"
;;; actually sets the head pointer of the queue in the empty queue case.

#-Lockfree-Deque
(defmacro constant-queue-enqueue (constant-queue thing)
  (let* ((queue-var (if (symbolp constant-queue)
                        constant-queue
                        (gensym)))
         (tail (gensym))
         (new-element (gensym)))
    `(let* (,@(if (neq queue-var constant-queue)
                  `((,queue-var ,constant-queue)))
            (,tail (constant-queue-tail ,queue-var))
            (,new-element (make-queue-element-macro ,queue-var ,tail ,thing)))
       (setf (queue-next-element ,tail) ,new-element)
       (setf (constant-queue-tail ,queue-var) ,new-element)
       ,new-element)))

;;; The PushRight operation inserts a new node at the rightmost position in the
;;; deque. The algorithm first repeatedly tries in lines R4-R13 to insert the
;;; new node (node) between the rightmost node (prev) and the tail node (next),
;;; by atomically changing the next pointer of the prev node. Before trying to
;;; update the next pointer, it assures in line R5 that the next node is still
;;; the very next node of prev, otherwise prev is updated by calling the Help-
;;; Insert function in R6, which updates the prev pointer of the next node.
;;; After the new node has been successfully inserted, it tries in lines P1-P13
;;; to update the prev pointer of the next node, following the same scheme as
;;; for the PushLeft operation.

#+(or Lockfree-Deque Lockfree-List)
(defmacro generate-*-push-common ((node next)
				  previous-element
				  next-element
				  copy-node
				  release-node
				  help-insert)
  `(progn
     (let ((backoff-limit backoff-min-delay))
       (loop as link1 = (,previous-element ,next)			  ; P1+P2
	     do
	 (when (or (atomic-reference-mark link1)			  ; P3
		   (atomic-reference-neq (,next-element ,node)
					 (make-atomic-reference ,next nil)))
	   (loop-finish))						  ; P4
	 (when (compare-and-swap (,previous-element ,next)
				 link1
				 (make-atomic-reference ,node nil))	  ; P5
	   (,copy-node ,node)						  ; P6
	   (,release-node (atomic-reference-object link1))		  ; P7
	   (when (atomic-reference-mark (,previous-element ,node))	  ; P8
	     (let ((prev2 (,copy-node ,node)))				  ; P9
	       (setq prev2 (,help-insert prev2 ,next))			  ; P10
	       (,release-node prev2)))					  ; P11
	   (loop-finish))						  ; P12
	 (back-off)))							  ; P13
     (,release-node ,next)						  ; P14
     (,release-node ,node)))						  ; P15

#+Lockfree-Deque
(defun-void constant-queue-push-common (node next)
  (generate-*-push-common (node next)
    queue-previous-element
    queue-next-element
    copy-queue-node
    release-queue-node
    help-insert-queue-node))

#+(or Lockfree-Deque Lockfree-List)
(defmacro generate-*-push-right ((structure
				  tail-element
				  previous-element
				  next-element
				  copy-node
				  read-node
				  help-insert
				  push-common)
				 create-action)
  `(progn
     (let* ((node ,create-action)					  ; R1
	    (next (,copy-node (,tail-element ,structure)))		  ; R2
	    (prev (,read-node (,previous-element next)))		  ; R3
	    (backoff-limit backoff-min-delay))
       (loop								  ; R4
	 (cond
	   ((atomic-reference-neq (,next-element prev)
				  (make-atomic-reference next nil))	  ; R5
	    (setq prev (,help-insert prev next)))			  ; R6
	   (t								  ; R7
	    (setf (,previous-element node)
		  (make-atomic-reference prev nil))			  ; R8
	    (setf (,next-element node)
		  (make-atomic-reference next nil))			  ; R9
	    (when (compare-and-swap (,next-element prev)
				    (make-atomic-reference next nil)
				    (make-atomic-reference node nil))	  ; R10
	      (,copy-node node)						  ; R11
	      (loop-finish))						  ; R12
	    (back-off))))						  ; R13
       (,push-common node next)						  ; R14
       node)))

#+Lockfree-Deque
(defun-simple constant-queue-push-right (constant-queue thing)
  (generate-*-push-right (constant-queue
			  constant-queue-tail
			  queue-previous-element
			  queue-next-element
			  copy-queue-node
			  read-queue-node
			  help-insert-queue-node
			  constant-queue-push-common)
    (create-queue-element thing)))

#+Lockfree-Deque
(defmacro constant-queue-enqueue (constant-queue thing)
  `(constant-queue-push-right ,constant-queue ,thing))

;;; The function `constant-queue-filo-enqueue' takes a constant queue and a
;;; thing to be enqueued, and enqueues that item in the queue for FILO
;;; dequeueing.  This function returns the new entry for the given thing in the
;;; queue.

#-Lockfree-Deque
(defmacro constant-queue-filo-enqueue (constant-queue thing)
  (let* ((queue-var (if (symbolp constant-queue) constant-queue (gensym)))
         (head (gensym))
         (new-element (gensym)))
    `(let* (,@(if (neq queue-var constant-queue)
                  `((,queue-var ,constant-queue)))
            (,head (constant-queue-head ,queue-var))
            (,new-element (make-queue-element-macro ,head ,queue-var ,thing)))
       (setf (constant-queue-head ,queue-var) ,new-element)
       (setf (queue-previous-element ,head) ,new-element)
       ,new-element)))

;;; The PushLeft operation inserts a new node at the leftmost position in the
;;; deque. The algorithm first repeatedly tries in lines L4-L14 to insert the
;;; new node (node) between the head node (prev) and the leftmost node (next),
;;; by atomically changing the next pointer of the head node. Before trying to
;;; update the next pointer, it assures in line L5 that the next node is still
;;; the very next node of head, otherwise next is updated in L6-L7. After the
;;; new node has been successfully inserted, it tries in lines P1-P13 to update
;;; the prev pointer of the next node. It retries until either i) it succeeds
;;; with the update, ii) it detects that either the next or new node is deleted,
;;; or iii) the next node is no longer directly next of the new node. In any of
;;; the two latter, the changes are due to concurrent Pop or Push operations,
;;; and the responsibility to update the prev pointer is then left to those. If
;;; the update succeeds, there is though the possibility that the new node was
;;; detected (and thus the prev pointer of the next node was possibly already
;;; updated by the concurrent Pop operation) directly before the CAS in line P5,
;;; and then the prev pointer is updated by calling the HelpInsert function in
;;; line P10.

#+(or Lockfree-Deque Lockfree-List)
(defmacro generate-*-push-left ((structure
				 head-element
				 previous-element
				 next-element
				 copy-node
				 read-node
				 release-node
				 push-common)
				create-action)
  `(progn
     (let* ((node ,create-action)					  ; L1
	    (prev (,copy-node (,head-element ,structure)))		  ; L2
	    (next (read-queue-node (queue-next-element prev)))		  ; L3
	    (backoff-limit backoff-min-delay))
       (loop								  ; L4
	 (cond
	   ((atomic-reference-neq (,next-element prev)
				  (make-atomic-reference next nil))	  ; L5
	    (,release-node next)					  ; L6
	    (setq next (,read-node (,next-element prev))))		  ; L7
	   (t								  ; L8
	    (setf (,previous-element node)
		  (make-atomic-reference prev nil))			  ; L9
	    (setf (,next-element node)
		  (make-atomic-reference next nil))			  ; L10
	    (when (compare-and-swap (,next-element prev)
				    (make-atomic-reference next nil)
				    (make-atomic-reference node nil))	  ; L11
	      (,copy-node node)						  ; L12
	      (loop-finish))						  ; L13
	    (back-off))))						  ; L14
       (,push-common node next)						  ; L15
       node)))

#+Lockfree-Deque
(defun-simple constant-queue-push-left (constant-queue thing)
  (generate-*-push-left (constant-queue
			 constant-queue-head
			 queue-previous-element
			 queue-next-element
			 copy-queue-node
			 read-queue-node
			 release-queue-node
			 constant-queue-push-common)
    (create-queue-element thing)))

#+Lockfree-Deque
(defmacro constant-queue-filo-enqueue (constant-queue thing)
  `(constant-queue-push-left ,constant-queue ,thing))

;;; The macro `constant-queue-dequeue' takes a constant queue and an optional
;;; value to return if the queue is empty.  It dequeues and returns the first
;;; element of the queue, or returns the given value if the queue is empty.
;;; Note that this is a NON-STANDARD MACRO in that the default value will only
;;; be evaluated if the queue is empty.

#-Lockfree-Deque
(defmacro constant-queue-dequeue (constant-queue &optional (default-value nil))
  (let ((queue-var (if (symbolp constant-queue)
                       constant-queue
                       (gensym)))
        (head (gensym))
        (datum (gensym))
        (new-head (gensym)))
    `(let* (,@(if (neq queue-var constant-queue)
                  `((,queue-var ,constant-queue)))
            (,head (constant-queue-head ,queue-var)))
       (if (eq ,head ,queue-var)
           (values ,default-value nil)
           (let ((,datum (queue-datum ,head))
                 (,new-head (queue-next-element ,head)))
             (setf (constant-queue-head ,queue-var) ,new-head)
             (setf (queue-previous-element ,new-head) ,queue-var)
             (reclaim-queue-element-macro ,head)
             (values ,datum t))))))

;;; The PopLeft operation tries to delete and return the value of the leftmost
;;; node in the deque. The algorithm first repeatedly tries in lines PL2-PL22 to
;;; mark the leftmost node (node) as deleted. Before trying to update the next
;;; pointer, it first assures in line PL4 that the deque is not empty, and secondly
;;; in line PL9 that the node is not already marked for deletion. If the deque
;;; was detected to be empty, the function returns. If node was marked for detection,
;;; it tries to update the next pointer of the prev node by calling the HelpDelete
;;; function, and then node is updated to be the leftmost node. If the prev pointer
;;; of node was incorrect, it tries to update it by calling the HelpInsert function.
;;; After the node has been successfully marked by the successful CAS operation in
;;; line PL13, it tries in line PL14 to update the next pointer of the prev node by
;;; calling the HelpDelete function, and in line PL16 to update the prev pointer of
;;; the next node by calling the HelpInsert function. After this, it tries in line
;;; PL23 to break possible cyclic references that includes node by calling the
;;; RemoveCrossReference function.

#+Lockfree-Deque
(defun constant-queue-pop-left (constant-queue &optional default-value)
  (let ((prev (copy-queue-node (constant-queue-head constant-queue)))	  ; PL1
	(tail (constant-queue-tail constant-queue))
	(node nil)
	(return-value default-value)
	(backoff-limit backoff-min-delay))
    (loop								  ; PL2
      (setq node (read-queue-node (queue-next-element prev)))		  ; PL3
      (when (eq node tail)						  ; PL4
	(release-queue-node node)					  ; PL5
	(release-queue-node prev)					  ; PL6
	(return-from constant-queue-pop-left
	  (values default-value nil)))					  ; PL7
      (let ((link1 (queue-next-element node)))				  ; PL8
	(cond
	  ((atomic-reference-mark link1)				  ; PL9
	   (help-delete-queue-node node)				  ; PL10
	   (release-queue-node node))					  ; PL11
	  (t
	   (when (compare-and-swap (queue-next-element node)
				   link1
				   (make-atomic-reference
				     (atomic-reference-object link1) t))  ; PL13
	     (help-delete-queue-node node)				  ; PL14
	     (let* ((next
		     (read-deleted-queue-node
		       (queue-next-element node)))			  ; PL15
		    (prev2 (help-insert-queue-node prev next)))		  ; PL16
	       (release-queue-node prev2)				  ; PL17
	       (release-queue-node next)				  ; PL18
	       (setq return-value (queue-datum node))			  ; PL19
	       (loop-finish)))						  ; PL20
	   (release-queue-node node)					  ; PL21
	   (back-off)))))						  ; PL22
    (remove-queue-cross-reference node)					  ; PL23
    (release-queue-node node)						  ; PL24
    (values return-value t)))						  ; PL25

#+Lockfree-Deque
(defmacro constant-queue-dequeue (constant-queue &optional (default-value nil))
  `(constant-queue-pop-left ,constant-queue ,default-value))

;;; The PopRight operation tries to delete and return the value of the rightmost
;;; node in the deque. The algorithm first repeatedly tries in lines PR2-PR19 to
;;; mark the rightmost node (node) as deleted. Before trying to update the next
;;; pointer, it assures i) in line PR4 that the node is not already marked for
;;; deletion, ii) in the same line that the prev pointer of the tail (next) node
;;; is correct, and iii) in line PR7 that the deque is not empty. If the deque
;;; was detected to be empty, the function returns. If node was marked for deletion
;;; or the prev pointer of the next node was incorrect, it tries to update the
;;; prev pointer of the next node by calling the HelpInsert function, and then
;;; node is updated to be the rightmost node. After the node has been successfully
;;; marked it follows the same scheme as the PopLeft operation.

#+Lockfree-Deque
(defun constant-queue-pop-right (constant-queue &optional default-value)
  (let* ((next (copy-queue-node (constant-queue-tail constant-queue)))	  ; PR1
	 (node (read-queue-node (queue-previous-element next)))		  ; PR2
	 (return-value default-value)
	 (backoff-limit backoff-min-delay))
    (loop								  ; PR3
      (cond
        ((atomic-reference-neq (queue-next-element node)
			       (make-atomic-reference next nil))	  ; PR4
	 (setq node (help-insert-queue-node node next)))		  ; PR5
	(t								  ; PR6
	 (when (eq node (constant-queue-head constant-queue))		  ; PR7
	   (release-queue-node node)					  ; PR8
	   (release-queue-node next)					  ; PR9
	   (return-from constant-queue-pop-right
	     (values default-value nil)))				  ; PR10
	 (when (compare-and-swap (queue-next-element node)
				 (make-atomic-reference next nil)
				 (make-atomic-reference next t))	  ; PR11
	   (help-delete-queue-node node)				  ; PR12
	   (let* ((prev
		   (read-deleted-queue-node
		     (queue-previous-element node)))			  ; PR13
		  (prev2 (help-insert-queue-node prev next)))		  ; PR14
	     (release-queue-node prev2)					  ; PR15
	     (release-queue-node next)					  ; PR16
	     (setq return-value (queue-datum node))			  ; PR17
	     (loop-finish)))						  ; PR18
	 (back-off))))							  ; PR19
    (remove-queue-cross-reference node)					  ; PR20
    (release-queue-node node)						  ; PR21
    (values return-value t)))						  ; PR22

#+Lockfree-Deque
(defmacro constant-queue-filo-dequeue (constant-queue &optional (default-value nil))
  `(constant-queue-pop-right ,constant-queue ,default-value))

;;; Helping and Back-Off

;;; The HelpDelete sub-procedure tries to set the deletion mark of the prev
;;; pointer and then atomically update the next pointer of the previous node
;;; of the to-be-deleted node, thus fulfilling step 2 and 3 of the overall
;;; node deletion scheme. The algorithm first ensures in line HD1-HD4 that
;;; the deletion mark on the prev pointer of the given node is set. It then
;;; repeatedly tries in lines HD8-HD34 to delete (in the sense of a chain of
;;; next pointers starting from the head node) the given marked node (node)
;;; by changing the next pointer from the previous non-marked node. First, we
;;; can safely assume that the next pointer of the marked node is always
;;; referring to a node (next) to the right and the prev pointer is always
;;; referring to a node (prev) to the left (not necessarily the first). Before
;;; trying to update the next pointer with the CAS operation in line HD30, it
;;; assumes in line HD9 that node is not already deleted, in line HD10 that
;;; the next node is not marked, in line HD16 that the prev node is not marked,
;;; and in HD24 that prev is the previous node of node. If next is marked, it
;;; is updated to be the next node. If prev is marked we might need to delete
;;; it before we can update prev to one of its previous nodes and proceed with
;;; the current deletion, but in order to avoid unnecessary and even possibly
;;; infinite recursion, HelpDelete is only called if a next pointer from a non-
;;; marked node to prev has been observed (i.e. lastlink.d is false). Otherwise
;;; if prev is not the previous node of node it is updated to be the next node.

#+(or Lockfree-Deque Lockfree-List)
(defmacro generate-help-delete ((node)
				previous-element
				next-element
				read-node
				read-deleted-node
				copy-node
				release-node
				help-delete)
  `(progn
     (loop as link1 = (,previous-element ,node) do			  ; HD1+HD2
       (when (or (atomic-reference-mark link1)				  ; HD3
		 (compare-and-swap (,previous-element ,node)		  ; HD4
				   link1
				   (make-atomic-reference
				     (atomic-reference-object link1) t)))
	 (loop-finish)))
     (let ((lastlink-deleted? t)					  ; HD5
	   (prev (,read-deleted-node (,previous-element ,node)))	  ; HD6
	   (next (,read-deleted-node (,next-element ,node)))		  ; HD7
	   (backoff-limit backoff-min-delay))
       (loop								  ; HD8
	 (when (eq prev next) (loop-finish))				  ; HD9
	 (cond
	   ((atomic-reference-mark (,next-element next))		  ; HD10
	    (let ((next2
		   (,read-deleted-node (,next-element next))))		  ; HD11
	      (,release-node next)					  ; HD12
	      (setq next next2)))					  ; HD13
	   (t
	    (let ((prev2 (,read-node (,next-element prev))))		  ; HD15
	      (cond
	        ((null prev2)						  ; HD16
		 (when (not lastlink-deleted?)				  ; HD17
		   (,help-delete prev) ; recursive call		  ; HD18
		   (setq lastlink-deleted? t))				  ; HD19
		 (setq prev2
		       (,read-deleted-node (,previous-element prev)))	  ; HD20
		 (,release-node prev)					  ; HD21
		 (setq prev prev2))					  ; HD22
		((neq prev2 ,node)					  ; HD24
		 (setq lastlink-deleted? nil)				  ; HD25
		 (,release-node prev)					  ; HD26
		 (setq prev prev2))					  ; HD27
		(t ; (eq prev2 node)
		 (,release-node prev2)					  ; HD29
		 (when (compare-and-swap (,next-element prev)		  ; HD30
					 (make-atomic-reference ,node nil)
					 (make-atomic-reference next nil))
		   (,copy-node next)					  ; HD31
		   (,release-node ,node)				  ; HD32
		   (loop-finish))					  ; HD33
		 (back-off)))))))					  ; HD34
       (,release-node prev)						  ; HD35
       (,release-node next))))						  ; HD36

#+Lockfree-Deque
(defun-void help-delete-queue-node (node)
  (generate-help-delete (node)
    queue-previous-element
    queue-next-element
    read-queue-node
    read-deleted-queue-node
    copy-queue-node
    release-queue-node
    help-delete-queue-node))

;;; The HelpInsert sub-function tries to update the prev pointer of a node and
;;; then return a reference to a possibly direct previous node, thus fulfilling
;;; step 2 of the overall insertion scheme or step 4 of the overall deletion
;;; scheme. The algorithm repeatedly tries in lines HI2-HI27 to correct the prev
;;; pointer of the given node (node), given a suggestion of a previous (not
;;; necessarily the directly previous) node (prev). Before trying to update the
;;; prev pointer with the CAS operation in line HI22, it assures in line HI4 that
;;; the prev node is not marked, in line HI13 that node is not marked, and in
;;; line HI16 that prev is the previous node of node. If prev is marked we might
;;; need to delete it before we can update prev to one of its previous nodes and
;;; proceed with the current insertion, but in order to avoid unnecessary
;;; recursion, HelpDelete is only called if a next pointer from a non-marked node
;;; to prev has been observed (i.e. lastlink.d is false). If node is marked, the
;;; procedure is aborted. Otherwise if prev is not the previous node of node it
;;; is updated to be the next node. If the update in line HI22 succeeds, there is
;;; though the possibility that the prev node was deleted (and thus the prev
;;; pointer of node was possibly already updated by the concurrent Pop operation)
;;; directly before the CAS operation. This is detected in line HI25 and then the
;;; update is possibly retried with a new prev node.

#+(or Lockfree-Deque Lockfree-List)
(defmacro generate-help-insert ((prev node)
				previous-element
				next-element
				read-node
				read-deleted-node
				copy-node
				release-node
				help-delete)
  `(progn
     (let ((backoff-limit backoff-min-delay)
	   (lastlink-deleted? t))					  ; HI1
       (loop as prev2 = (,read-node (,next-element ,prev))		  ; HI3+HI3
	     do
	 (cond
	   ((null prev2)						  ; HI4
	    (when (not lastlink-deleted?)				  ; HI5
	      (,help-delete ,prev)					  ; HI6
	      (setq lastlink-deleted? t))				  ; HI7
	    (setq prev2
		  (,read-deleted-node (,previous-element ,prev)))	  ; HI8
	    (,release-node ,prev)					  ; HI9
	    (setq ,prev prev2))						  ; HI10
	   (t
	    (let ((link1 (,previous-element ,node)))			  ; HI12
	      (when (atomic-reference-mark link1)			  ; HI13
		(,release-node prev2)					  ; HI14
		(return ,prev))						  ; HI15
	      (cond
	        ((neq prev2 ,node)					  ; HI16
		 (setq lastlink-deleted? nil)				  ; HI17
		 (,release-node ,prev)					  ; HI18
		 (setq ,prev prev2))					  ; HI19
		(t
		 (,release-node prev2)					  ; HI21
		 (when (compare-and-swap (,previous-element ,node)	  ; HI22
					 link1
					 (make-atomic-reference ,prev nil))
		   (,copy-node ,prev)					  ; HI23
		   (,release-node (atomic-reference-object link1))	  ; HI24
		   (unless (atomic-reference-mark
			     (,previous-element ,prev))			  ; HI25
		     (return ,prev)))					  ; HI26
		 (back-off))))))))))					  ; HI27

#+Lockfree-Deque
(defun-simple help-insert-queue-node (prev node)
  (generate-help-insert (prev node)
    queue-previous-element
    queue-next-element
    read-queue-node
    read-deleted-queue-node
    copy-queue-node
    release-queue-node
    help-delete-queue-node))

;;; The RemoveCrossReference sub-procedure tries to break cross-references
;;; between the given node (node) and any of the nodes that it references, by
;;; repeatedly updating the prev and next pointer as long as they reference a
;;; marked node. First, we can safely assume that the prev or next field of
;;; node is not concurrently updated by any other operation, as this procedure
;;; is only called by the main operation that deleted the node and both the
;;; next and prev pointers are marked and thus any concurrent update using CAS
;;; will fail. Before the procedure is finished, it assures in the next node
;;; (next) is not marked. As long as prev is marked it is traversed to the left,
;;; and as long as next is marked it is traversed to the right, while
;;; continuously updating the prev or next field of node in lines RC5 or RC11.

#+(or Lockfree-Deque Lockfree-List)
(defmacro generate-remove-cross-reference ((node)
					   previous-element
					   next-element
					   read-deleted-node
					   release-node)
  `(progn
     (loop as prev = (atomic-reference-object (,previous-element ,node))  ; RC1
	   do								  ; RC2
       (cond
	 ((atomic-reference-mark (,next-element prev))			  ; RC3
	  (let ((prev2 (,read-deleted-node
			 (,previous-element prev))))			  ; RC4
	    (setf (,previous-element ,node)
		  (make-atomic-reference prev2 t))			  ; RC5
	    (,release-node prev)))					  ; RC6
	 (t
	  (let ((next (atomic-reference-object (,next-element ,node))))	  ; RC8
	    (if (atomic-reference-mark (,next-element next))		  ; RC9
		(let ((next2 (,read-deleted-node
			       (,next-element next))))			  ; RC10
		  (setf (,next-element ,node)
			(make-atomic-reference next2 t))		  ; RC11
		  (,release-node next))					  ; RC12
	      (loop-finish))))))))					  ; RC14

#+Lockfree-Deque
(defun-void remove-queue-cross-reference (node)
  (generate-remove-cross-reference (node)
    queue-previous-element
    queue-next-element
    read-deleted-queue-node
    release-queue-node))

;;; The `InsertBefore' operation inserts a new node directly before the node
;;; positioned by the given cursor and later changes the cursor to position
;;; the inserted node. If the node positioned by the cursor is the head
;;; dummy node, the new node will be inserted directly after the head dummy
;;; node. The algorithm checks in line IB1 if the cursor position is equal
;;; to the head dummy node, and consequently then calls the `InsertAfter'
;;; operation to insert the new node directly after the head dummy node.
;;; The algorithm repeatedly tries in lines IB4-IB13 to insert the new node
;;; (node) between the previous node (prev) of the cursor and the cursor
;;; positioned node, by atomically changing the next pointer of the prev node
;;; to instead point to the new node. If the node positioned by the cursor is
;;; deleted this is deleted in line IB4 and the cursor is updated by calling
;;; the `Next' function. If the update of the next pointer of the prev node
;;; by using the CAS operation in line IB8 fails, this is because either the
;;; prev node is no longer the directly previous node of the cursor
;;; positioned node, or that the cursor positioned node is deleted. If the
;;; prev node is no longer the directly previous node this is deleted in
;;; line IB11 and then the `HelpInsert' function is called in order to
;;; update the prev pointer of the cursor positioned node. If the update
;;; using CAS in line IB8 succeeds, the cursor position is set to the new
;;; node in line IB15 and the prev pointer of the previous cursor positioned
;;; node is updated by calling the `HelpInsert' function in line IB16. The
;;; linearizability point of the InsertBefore operation is the successful
;;; CAS operation in line IB8, or equal to the linearizability point of the
;;; InsertBefore operation if that operation was called in line IB1.

#+(or Lockfree-Deque Lockfree-List)
(defmacro generate-*-insert-before ((function-name structure cursor
				     structure-head
				     structure-next
				     previous-element next-element
				     read-deleted-node copy-node
				     release-node help-insert)
				    create-action
				    insert-after-action)
  `(progn
     (when (eq ,cursor (,structure-head ,structure))
       (return-from ,function-name ,insert-after-action))		  ; IB1
     (let ((node ,create-action)					  ; IB2
	   (backoff-limit backoff-min-delay))
       (loop doing							  ; IB3
	 (when (atomic-reference-mark (,next-element ,cursor))
	   (setq ,cursor (,structure-next ,cursor ,structure)))		  ; IB4
	 (let ((prev (,read-deleted-node
		       (,previous-element ,cursor))))			  ; IB5
	   (setf (,previous-element node)
		 (make-atomic-reference prev nil))			  ; IB6
	   (setf (,next-element node)
		 (make-atomic-reference ,cursor nil))			  ; IB7
	   (when (compare-and-swap (,next-element prev)
				   (make-atomic-reference ,cursor nil)
				   (make-atomic-reference node nil))	  ; IB8
	     (,copy-node node)						  ; IB9
	     (loop-finish))						  ; IB10
	   (when (atomic-reference-neq (,next-element prev)
				       (make-atomic-reference ,cursor nil))
	     (setq prev (,help-insert prev ,cursor)))			  ; IB11
	   (,release-node prev)						  ; IB12
	   (back-off)))							  ; IB13
       (let ((next ,cursor))						  ; IB14
	 #+ignore
	 (setq cursor (,copy-node node))				  ; IB15
	 (setq node (,help-insert node next))				  ; IB16
	 (,release-node node)						  ; IB17
	 #+ignore
	 (,release-node next))						  ; IB18
       node)))

#+Lockfree-Deque
(defun-simple constant-queue-insert-before (constant-queue cursor thing)
  (generate-*-insert-before (constant-queue-insert-before constant-queue cursor
			     constant-queue-head
			     constant-queue-next
			     queue-previous-element
			     queue-next-element
			     read-deleted-queue-node
			     copy-queue-node
			     release-queue-node
			     help-insert-queue-node)
    (create-queue-element thing)
    (constant-queue-insert-after constant-queue cursor thing)))

#-Lockfree-Deque
(defmacro constant-queue-insert-before (constant-queue cursor thing)
  (let* ((queue-var (if (symbolp constant-queue)
			constant-queue
		        (gensym)))
         (head (gensym))
         (new-element (gensym)))
    `(let* (,@(if (neq queue-var constant-queue)
                  `((,queue-var ,constant-queue))))
       (if (eq ,cursor ,queue-var)
	   (constant-queue-enqueue ,queue-var ,thing)
	 (let* ((,head (queue-previous-element ,cursor))
		(,new-element (make-queue-element-macro ,cursor ,head ,thing)))
	   (setf (queue-previous-element ,cursor) ,new-element)
	   (if (eq ,head ,queue-var) ; cursor is head
	       (setf (constant-queue-head ,queue-var) ,new-element)
	     (setf (queue-next-element ,head) ,new-element))
	   ,new-element)))))

;;; The `InsertAfter' operation inserts a new node directly after the node
;;; positioned by the given cursor and later changes the cursor to position
;;; inserted node. If the node positioned by the cursor is the tail dummy
;;; node, the new node will be inserted directly before the tail dummy node.
;;; The algorithm checks in line IA1 if the cursor position is equal to the
;;; tail dummy node, and consequently then calls the `InsertBefore' operation
;;; to insert the new node directly after the head dummy node. The algorithm
;;; repeatedly tries in lines IA4-IA14 to insert the new node (node) between
;;; the cursor positioned node and the next node (next) of the cursor, by
;;; atomically changing the next pointer of the cursor positioned node to
;;; instead point to the new node. If the update of the next pointer of the
;;; cursor positioned node by using the CAS operation in line IA7 fails, this
;;; is because either the next node is no longer the directly next node of
;;; the cursor positioned node, or that the cursor positioned node is deleted.
;;; If the cursor positioned node is deleted, the operation to insert directly
;;; after the cursor position now becomes the problem of inserting
;;; directly before the node that represents the cursor position according to
;;; [Def 1]*. It is detected in line IA11 if the cursor positioned node is
;;; deleted and then it calls the `InsertBefore' operation in line IA13. If
;;; the update using CAS in line IA7 succeeds, the cursor position is set to
;;; the new node in line IA15 and the prev pointer of the previous cursor
;;; positioned node is updated by calling the `HelpInsert' function in line
;;; IA16. The linearizability point of the InsertAfter operation is the
;;; successful CAS operation in line IA7, or equal to the linearizability
;;; point of the InsertAfter operation if that operation was called in line
;;; IA1 or IA13.

#+(or Lockfree-Deque Lockfree-List)
(defmacro generate-*-insert-after ((function-name structure cursor
				    structure-tail
				    previous-element
				    next-element
				    read-deleted-node copy-node
				    release-node help-insert)
				   create-action
				   insert-before-action)
  `(progn
     (when (eq ,cursor (,structure-tail ,structure))
       (return-from ,function-name ,insert-before-action))		  ; IA1
     (let ((node ,create-action)					  ; IA2
	   (next nil)
	   (backoff-limit backoff-min-delay))
       (loop doing							  ; IA3
	 (setq next (,read-deleted-node (,next-element ,cursor)))	  ; IA4
	 (setf (,previous-element node)
	       (make-atomic-reference ,cursor nil))			  ; IA5
	 (setf (,next-element node)
	       (make-atomic-reference next nil))			  ; IA6
	 (when (compare-and-swap (,next-element ,cursor)
				 (make-atomic-reference next nil)
				 (make-atomic-reference node nil))	  ; IA7
	   (,copy-node node)						  ; IA8
	   (loop-finish))						  ; IA9
	 (,release-node next)						  ; IA10
	 (when (atomic-reference-mark (,next-element ,cursor))		  ; IA11
	   (,release-node node)						  ; IA12
	   (return-from ,function-name ,insert-before-action))		  ; IA13
	 (back-off))							  ; IA14
       (,copy-node cursor) ; old: node					  ; IA15
       (setq node (,help-insert node next))				  ; IA16
       (,release-node node)						  ; IA17
       (,release-node next)						  ; IA18
       node)))


#+Lockfree-Deque
(defun-simple constant-queue-insert-after (constant-queue cursor thing)
  (generate-*-insert-after (constant-queue-insert-after constant-queue cursor
			    constant-queue-tail
			    queue-previous-element
			    queue-next-element
			    read-deleted-queue-node
			    copy-queue-node
			    release-queue-node
			    help-insert-queue-node)
    (create-queue-element thing)
    (constant-queue-insert-before constant-queue cursor thing)))

#-Lockfree-Deque
(defmacro constant-queue-insert-after (constant-queue cursor thing)
  (let* ((queue-var (if (symbolp constant-queue)
                        constant-queue
                        (gensym)))
	 (tail (gensym))
         (new-element (gensym)))
    `(let* (,@(if (neq queue-var constant-queue)
                  `((,queue-var ,constant-queue))))
       (if (eq ,cursor ,queue-var)
	   (constant-queue-filo-enqueue ,queue-var ,thing)
	 (let* ((,tail (queue-next-element ,cursor))
		(,new-element (make-queue-element-macro ,tail ,cursor ,thing)))
	   (setf (queue-next-element ,cursor) ,new-element)
	   (if (eq ,tail ,queue-var) ; cursor is tail
	       (setf (constant-queue-tail ,queue-var) ,new-element)
	     (setf (queue-previous-element ,tail) ,new-element))
	   ,new-element)))))

;;; The substitution macro `requeue-queue-element' takes a constant-queue and a
;;; queue-element.  The queue-element is removed from its current constant-queue
;;; and enqueued onto the end of the given constant-queue.  Note that the given
;;; constant-queue can either be the current queue for this queue-element, or it
;;; can be an entirely different constant queue.

#-Lockfree-Deque
(def-substitution-macro requeue-queue-element (constant-queue queue-element)
  (let ((old-next-element (queue-next-element queue-element))
        (old-previous-element (queue-previous-element queue-element)))
    (setf (queue-previous-element old-next-element) old-previous-element)
    (setf (queue-next-element old-previous-element) old-next-element))
  (let ((old-tail (constant-queue-tail constant-queue)))
    (setf (queue-next-element queue-element) constant-queue)
    (setf (queue-previous-element queue-element) old-tail)
    (setf (queue-next-element old-tail) queue-element)
    (setf (constant-queue-tail constant-queue) queue-element))
  nil)

;;; The substitution macro `merge-constant-queues' takes two constants queues,
;;; and appends the tasks from the second constant queue onto the end of the
;;; queue of tasks stored in the first constant queue.  After this macro, the
;;; second constant queue will always be empty.

#-Lockfree-Deque
(def-substitution-macro merge-constant-queues (queue-to-fill queue-to-empty)
  (unless (constant-queue-empty-p queue-to-empty)
    (let ((head (constant-queue-head queue-to-empty))
          (tail (constant-queue-tail queue-to-empty)))
      (setf (constant-queue-head queue-to-empty) queue-to-empty)
      (setf (constant-queue-tail queue-to-empty) queue-to-empty)
      (cond ((constant-queue-empty-p queue-to-fill)
             (setf (constant-queue-head queue-to-fill) head)
             (setf (constant-queue-tail queue-to-fill) tail)
             (setf (queue-previous-element head) queue-to-fill)
             (setf (queue-next-element tail) queue-to-fill))
            (t
             (let ((old-tail (constant-queue-tail queue-to-fill)))
               (setf (queue-next-element old-tail) head)
               (setf (queue-previous-element head) old-tail)
               (setf (constant-queue-tail queue-to-fill) tail)
               (setf (queue-next-element tail) queue-to-fill))))))
  #+development
  (unless (constant-queue-empty-p queue-to-empty)
    (error "constant queue not empty?!"))
  nil)

;;; The macro `delete-queue-element' takes a constant queue element and deletes
;;; it from its constant queue.  It also reclaims the given element.

#-Lockfree-Deque
(defmacro delete-queue-element (constant-queue-element)
  (let* ((element-var (if (symbolp constant-queue-element)
                          constant-queue-element
                          (gensym)))
         (next (gensym))
         (previous (gensym)))
    `(let* (,@(if (neq element-var constant-queue-element)
                  `((,element-var ,constant-queue-element)))
            (,next (queue-next-element ,element-var))
            (,previous (queue-previous-element ,element-var)))
       (setf (queue-next-element ,previous) ,next)
       (setf (queue-previous-element ,next) ,previous)
       (prog1 (queue-datum ,element-var)
	 (reclaim-queue-element-macro ,element-var)))))

#-Lockfree-Deque
(defmacro constant-queue-delete (queue-element constant-queue)
  (declare (ignore constant-queue))
  `(delete-queue-element ,queue-element))

;;; The `Delete' operation tries to delete the non-dummy node referenced by
;;; the given cursor and returns the value if successful, otherwise a non-
;;; value is returned. If the cursor positioned node is equal to any of the
;;; dummy nodes this is detected in line D1 and a non-value is returned. The
;;; algorithm repeatedly tries in line D3-D5 to set the deletion mark of the
;;; next pointer of the cursor positioned node. If the deletion mark is
;;; already set, this is detected in line D4 and a non-value is returned. If
;;; the CAS operation in line D5 succeeds, the deletion process is completed
;;; by calling the HelpDelete procedure in line D6 and the HelpInsert function
;;; in line D8. In order to avoid possible problems with cyclic garbage the
;;; RemoveCrossReference procedure in called in line D11. The value of the
;;; deleted node is read in line D10 and the value returned in line D12. The
;;; linearizability point of a Delete function that returns a value is the
;;; successful CAS operation in line D5. The linearizability point of a Delete
;;; function that returns a non-value is the read sub-operation of the next
;;; pointer in line D3, unless the node positioned by the cursor was the head
;;; or tail dummy node when the linearizability point instead is line D1.

#+(or Lockfree-Deque Lockfree-List)
(defmacro generate-*-delete ((cursor structure)
			     head-element
			     tail-element
			     next-element
			     previous-element
			     copy-node
			     release-node
			     help-delete
			     help-insert
			     structure-datum
			     remove-cross-reference
			     structure-delete)
  `(progn
     (when (and ,structure
		(or (eq ,cursor (,head-element ,structure))
		    (eq ,cursor (,tail-element ,structure))))
       (return-from ,structure-delete (values nil nil)))		  ; D1
     (loop as link1 = (,next-element ,cursor)				  ; D3
	   do
       (when (atomic-reference-mark link1)				  ; D4
	 (return (values nil nil)))
       (when (compare-and-swap (,next-element ,cursor)
			       link1
			       (make-atomic-reference
				 (atomic-reference-object link1) t))	  ; D5
	 (,help-delete ,cursor)						  ; D6
	 (let ((prev
		(,copy-node (atomic-reference-object
			      (,previous-element ,cursor)))))		  ; D7
	   (setq prev
		 (,help-insert prev
			       (atomic-reference-object link1)))	  ; D8
	   (,release-node prev)						  ; D9
	   (let ((value (,structure-datum ,cursor)))			  ; D10
	     (,remove-cross-reference ,cursor)				  ; D11
	     (return (values value t))))))))				  ; D12

#+Lockfree-Deque
(defun constant-queue-delete (cursor &optional constant-queue)
  (generate-*-delete (cursor constant-queue)
		     constant-queue-head
		     constant-queue-tail
		     queue-next-element
		     queue-previous-element
		     copy-queue-node
		     release-queue-node
		     help-delete-queue-node
		     help-insert-queue-node
		     queue-datum
		     remove-queue-cross-reference
		     constant-queue-delete))

#+Lockfree-Deque
(defmacro delete-queue-element (constant-queue-element)
  `(constant-queue-delete ,constant-queue-element))

;; find the first matched datum and delete it from constant-queue
(defun-void constant-queue-search-and-delete (constant-queue datum)
  (loop with head = (constant-queue-head constant-queue)
	for queue-element = #-Lockfree-Deque head
			    #+Lockfree-Deque (constant-queue-next head constant-queue)
		       then (constant-queue-next queue-element constant-queue)
	until #-Lockfree-Deque (eq queue-element constant-queue)
	      #+Lockfree-Deque (null queue-element)
	when (eq datum (queue-datum queue-element))
	  do (constant-queue-delete queue-element constant-queue)
	     (loop-finish)))

;; find all matched data and delete them from constant queue
(defun-void constant-queue-search-and-delete-all (constant-queue datum)
  (loop with head = (constant-queue-head constant-queue)
	for queue-element = #-Lockfree-Deque head
			    #+Lockfree-Deque (constant-queue-next head constant-queue)
		       then next-queue-element
	until #-Lockfree-Deque (eq queue-element constant-queue)
	      #+Lockfree-Deque (null queue-element)
	for next-queue-element = (constant-queue-next queue-element constant-queue)
	when (eq datum (queue-datum queue-element))
	  do (constant-queue-delete queue-element constant-queue)))

#+Lockfree-Deque
(defun requeue-queue-element (constant-queue queue-element element-queue)
  (let ((value (queue-datum queue-element)))
    (constant-queue-delete queue-element element-queue)
    (constant-queue-enqueue constant-queue value))
  nil)

;;; The development function `check-constant-queue-ok' takes a constant queue
;;; and checks that it's elements are in a circular list and that they become
;;; circular within fewer than `constant-queue-check-limit' elements.

#+development
(defconstant constant-queue-check-limit 131072) ; increased for HTWOS

;;; The loop path `constant-queue-element' is used to iterate over all
;;; constant-queue-elements within a constant queue.  During this iteration it
;;; is OK to call delete-queue-element on the current queue element given by the
;;; iteration, but any other modifications to the constant-queue being iterated
;;; have undefined effect.

(define-loop-path (constant-queue-element) constant-queue-elements-of (of))

(defun-for-macro constant-queue-elements-of
    (path-name variable data-type prep-phrases inclusive?
               allowed-preposistions data)
  (declare (ignore data-type data allowed-preposistions))
  (when (null prep-phrases)
    (error "OF is missing in ~S iteration path of ~S."
           path-name variable))
  (when inclusive?
    (error "Inclusive stepping is not supported in ~s path of ~s ~
            (prep-phrase = ~s)"
           path-name variable prep-phrases))
  (let* ((queue (make-symbol "QUEUE"))
         (next-queue-element (make-symbol "NEXT-QUEUE-ELEMENT"))
         (init-bindings
           `((,queue ,(second (car prep-phrases)))
             (,next-queue-element nil)
             (,variable nil)))
         (prologue-forms
           `((setq ,next-queue-element
                   #-Lockfree-Deque (constant-queue-head ,queue)
                   #+Lockfree-Deque (constant-queue-next
                                      (constant-queue-head ,queue) ,queue))))
         (pre-step-tests
	   #-Lockfree-Deque
	   `(eq ,next-queue-element ,queue)
	   #+Lockfree-Deque
           `(null ,next-queue-element))
         (steppings nil)
         (post-step-tests nil)
         (post-step-settings
           `(,variable (queue-datum ,next-queue-element)
             ,next-queue-element
             (constant-queue-next ,next-queue-element ,queue))))
    `(,init-bindings
      ,prologue-forms
      ,pre-step-tests
      ,steppings
      ,post-step-tests
      ,post-step-settings)))


;;; The development function `constant-queue-elements' returns a list of
;;; the values queued in the given constant queue.

#+development
(defun constant-queue-elements (constant-queue)
  (loop for element being each constant-queue-element of constant-queue
        collect element))

(defun constant-queue-length (constant-queue)
  (if (null constant-queue)
      0
    (loop for element being each constant-queue-element of constant-queue
	  count element)))

#+development
(defun describe-constant-queue (constant-queue)
  "Display all queue elements in a constant queue (with head and tail), then ~
return the number of elements (not include head and tail)."
  (flet ((print-one (element)
	   #-Lockfree-Deque
	   (format t "~A: next: ~A, prev: ~A, data: ~A~%"
		   (%pointer element)
		   (queue-next-element element)
		   (queue-previous-element element)
		   (queue-datum element))
	   #+Lockfree-Deque
	   (format t "~A: next: ~A, prev: ~A, data: ~A, ref-count: ~D (claim-bit: ~D)~%"
		   (%pointer element)
		   (queue-next-element element)
		   (queue-previous-element element)
		   (queue-datum element)
		   (reference-count element)
		   (claim-bit element))))
    (let ((element-list nil)
	  (head (constant-queue-head constant-queue))
	  #+Lockfree-Deque
	  (tail (constant-queue-tail constant-queue)))
      (loop for element = #-Lockfree-Deque head
			  #+Lockfree-Deque (queue-next-element-real head)
			then (queue-next-element-real element)
			until #-Lockfree-Deque (eq element constant-queue)
			      #+Lockfree-Deque (eq element tail)
	    initially
	      #-Lockfree-Deque ()
	      #+Lockfree-Deque (print-one head)
	    do
	(print-one element)
	(push element element-list)
	    finally
	      #+Lockfree-Deque (print-one tail)
	      (return (nreverse element-list))))))

;; reverse the elements and reclaim the argument
(defun-simple constant-queue-nreverse (constant-queue)
  (let ((new-constant-queue
	 (make-empty-constant-queue)))
    (loop for block being each constant-queue-element of constant-queue
	  do
      (constant-queue-filo-enqueue new-constant-queue block) ; push-left
          finally
	    (reclaim-constant-queue constant-queue)
	    (return new-constant-queue))))

(defun-simple constant-queue-nth (n constant-queue)
  (loop for count fixnum = 0 then (+f count 1)
	for block being each constant-queue-element of constant-queue
	when (=f count n)
	do (return block)))
