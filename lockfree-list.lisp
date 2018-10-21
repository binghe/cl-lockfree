(in-package :lockfree)

(defmacro make-list-element-macro (queue-next-element queue-previous-element queue-datum)
  `(vector 1 ,queue-next-element ,queue-previous-element ,queue-datum))

(defun make-list-element (queue-next-element queue-previous-element queue-datum)
  (make-list-element-macro queue-next-element queue-previous-element queue-datum))

(defmacro reclaim-list-element-macro (list-element)
  (declare (ignore list-element))
  nil) ; no-op

(defmacro reclaim-list-element (list-element)
  (reclaim-list-element-macro list-element))

(defmacro reference-count-and-claim-bit (list-element)
  `(svref ,list-element 0))

(defmacro queue-next-element (list-element)
  `(svref ,list-element 1))

(defmacro queue-previous-element (list-element)
  `(svref ,list-element 2))

(defmacro queue-datum (list-element)
  `(svref ,list-element 3))

(defmacro reference-count (list-element)
  `(ash (queue-reference-count-and-claim-bit ,list-element) -1))

(defmacro claim-bit (list-element)
  `(ldb (byte 1 0) (reference-count-and-claim-bit ,list-element)))

(defconstant +lockfree-list-marker+ '(lockfree-list-marker))

(defrun lockfree-list-p (thing)
  (and (simple-vector-p thing)
       (=f (length (the simple-vector thing)) 4)
       (eq (queue-datum thing) lockfree-list-marker)))

(defmacro safe-queue-read (place)
  (let ((q (gensym)))
    `(loop for ,q = ,place do
       (unless ,q (return nil))
       (atomic-incf (reference-count-and-claim-bit ,place) 2)
       (if (eq ,q ,place)
	   (return ,q)
	 (release-queue-node ,q)))))

(defmacro copy-queue-node (node-or-place) ; COPY_NODE
  `(safe-queue-read ,node-or-place))

(defun read-queue-node (reference) ; READ_NODE
  (multiple-value-bind (node mark)
      (get-atomic-reference reference)
    (unless mark
      (safe-queue-read node))))

;; READ_DEL_NODE
(defun read-deleted-queue-node (reference)
  (let ((node (get-atomic-reference reference)))
    (safe-queue-read node)
    node))

(defun create-list-element (thing)
  (let ((node (make-list-element-macro nil nil nil)))			  ; C1
    (setq node (safe-queue-read node))
    (clear-lowest-bit (reference-count-and-claim-bit node))
    (setf (queue-datum node) thing)					  ; C2
    node))								  ; C3

(defun release-queue-node (node)
  (when (null node)
    (return-from release-queue-node))
  (when (=f 0 (decrement-and-test-and-set (reference-count-and-claim-bit node)))
    (return-from release-queue-node))
  (release-reference node)
  (reclaim-list-element-macro node))

(defconstant lockfree-list-head-marker '(lockfree-list-head-marker))
(defconstant lockfree-list-tail-marker '(lockfree-list-tail-marker))

(defmacro queue-next-element-real (list-element)
  `(atomic-reference-object
     (queue-next-element ,list-element)))

(defmacro queue-previous-element-real (list-element)
  `(atomic-reference-object
     (queue-previous-element ,list-element)))

(defmacro lockfree-list-head (list-element)
  `(queue-next-element ,list-element))

(defmacro lockfree-list-tail (list-element)
  `(queue-previous-element ,list-element))

(defun make-empty-lockfree-list ()
  (let ((new-queue (make-list-element-macro
		     nil nil lockfree-list-marker))
	(head (make-list-element-macro
		nil (make-atomic-reference nil) lockfree-list-head-marker))
	(tail (make-list-element-macro
		(make-atomic-reference nil) nil lockfree-list-tail-marker)))
    (setq head (safe-queue-read head)
	  tail (safe-queue-read tail))
    (clear-lowest-bit (reference-count-and-claim-bit head))
    (clear-lowest-bit (reference-count-and-claim-bit tail))
    (setf (queue-next-element head) (make-atomic-reference tail))
    (setf (queue-previous-element tail) (make-atomic-reference head))
    (setf (lockfree-list-head new-queue) head)
    (setf (lockfree-list-tail new-queue) tail)
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

(defun lockfree-list-next (cursor lockfree-list)
  (generate-*-next (cursor lockfree-list)
    lockfree-list-tail
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

(defun lockfree-list-previous (cursor lockfree-list)
  (generate-*-previous (cursor lockfree-list)
    lockfree-list-head
    queue-next-element
    queue-previous-element
    read-deleted-queue-node
    release-queue-node
    help-insert-queue-node
    lockfree-list-next))

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

(defun lockfree-list-read (cursor &optional lockfree-list)
  (if (or (eq cursor (lockfree-list-head-if lockfree-list))		  ; RD1
	  (eq cursor (lockfree-list-tail-if lockfree-list)))
      nil
    (let ((value (queue-datum cursor)))					  ; RD2
      (if (atomic-reference-mark (queue-next-element cursor))		  ; RD3
	  nil
	value))))							  ; RD4

(defun clear-lockfree-list (lockfree-list)
  (let ((head (lockfree-list-head lockfree-list))
        (tail (lockfree-list-tail lockfree-list)))
    (loop with next-element-structure = nil
	  for element-structure = (queue-next-element-real head)
	                        then next-element-structure
	  until (eq element-structure tail)
	  do
      (setf next-element-structure (queue-next-element-real element-structure))
      (reclaim-list-element-macro element-structure))
    (setf (queue-next-element head)
          (make-atomic-reference tail))
    (setf (queue-previous-element tail)
          (make-atomic-reference head))
    lockfree-list))

(defun reclaim-lockfree-list (lockfree-list)
  (let ((head (lockfree-list-head lockfree-list))
        (tail (lockfree-list-tail lockfree-list)))
    (loop for element = head
                   then (prog1 (queue-next-element-real element)
                          (reclaim-list-element-macro element))
          until (eq element tail)
          finally (reclaim-list-element-macro element)))
  (setf (queue-datum lockfree-list) nil)
  (reclaim-list-element-macro lockfree-list)
  nil)

(defmacro lockfree-list-peek (lockfree-list &optional (default-value nil))
  (let ((queue-var (if (symbolp lockfree-list)
		       lockfree-list
		     (make-symbol "QUEUE")))
	(head (make-symbol "HEAD"))
	(first (make-symbol "FIRST")))
    `(let* (,@(if (neq queue-var lockfree-list)
		  `((,queue-var ,lockfree-list)))
	    (,head (lockfree-list-head ,queue-var))
	    (,first (lockfree-list-next ,head ,queue-var)))
       (if ,first
	   (lockfree-list-read ,first ,queue-var)
         ,default-value))))

;;; The substitution macro `lockfree-list-empty-p' returns whether or not the
;;; queue is empty.  If you want the datum of the first queue entry, call
;;; lockfree-list-peek.

(def-substitution-macro lockfree-list-empty-p (lockfree-list)
  #-Lockfree-Deque
  (eq (lockfree-list-head lockfree-list) lockfree-list)
  #+Lockfree-Deque
  (null (lockfree-list-next
          (lockfree-list-head lockfree-list) lockfree-list)))

(def-substitution-macro lockfree-list-non-empty-p (lockfree-list)
  (not (lockfree-list-empty-p lockfree-list)))

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
(defun-void lockfree-list-push-common (node next)
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
(defun-simple lockfree-list-push-right (lockfree-list thing)
  (generate-*-push-right (lockfree-list
			  lockfree-list-tail
			  queue-previous-element
			  queue-next-element
			  copy-queue-node
			  read-queue-node
			  help-insert-queue-node
			  lockfree-list-push-common)
    (create-list-element thing)))

#+Lockfree-Deque
(defmacro lockfree-list-enqueue (lockfree-list thing)
  `(lockfree-list-push-right ,lockfree-list ,thing))

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
(defun-simple lockfree-list-push-left (lockfree-list thing)
  (generate-*-push-left (lockfree-list
			 lockfree-list-head
			 queue-previous-element
			 queue-next-element
			 copy-queue-node
			 read-queue-node
			 release-queue-node
			 lockfree-list-push-common)
    (create-list-element thing)))

#+Lockfree-Deque
(defmacro lockfree-list-filo-enqueue (lockfree-list thing)
  `(lockfree-list-push-left ,lockfree-list ,thing))

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
(defun lockfree-list-pop-left (lockfree-list &optional default-value)
  (let ((prev (copy-queue-node (lockfree-list-head lockfree-list)))	  ; PL1
	(tail (lockfree-list-tail lockfree-list))
	(node nil)
	(return-value default-value)
	(backoff-limit backoff-min-delay))
    (loop								  ; PL2
      (setq node (read-queue-node (queue-next-element prev)))		  ; PL3
      (when (eq node tail)						  ; PL4
	(release-queue-node node)					  ; PL5
	(release-queue-node prev)					  ; PL6
	(return-from lockfree-list-pop-left
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
(defmacro lockfree-list-dequeue (lockfree-list &optional (default-value nil))
  `(lockfree-list-pop-left ,lockfree-list ,default-value))

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
(defun lockfree-list-pop-right (lockfree-list &optional default-value)
  (let* ((next (copy-queue-node (lockfree-list-tail lockfree-list)))	  ; PR1
	 (node (read-queue-node (queue-previous-element next)))		  ; PR2
	 (return-value default-value)
	 (backoff-limit backoff-min-delay))
    (loop								  ; PR3
      (cond
        ((atomic-reference-neq (queue-next-element node)
			       (make-atomic-reference next nil))	  ; PR4
	 (setq node (help-insert-queue-node node next)))		  ; PR5
	(t								  ; PR6
	 (when (eq node (lockfree-list-head lockfree-list))		  ; PR7
	   (release-queue-node node)					  ; PR8
	   (release-queue-node next)					  ; PR9
	   (return-from lockfree-list-pop-right
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
(defmacro lockfree-list-filo-dequeue (lockfree-list &optional (default-value nil))
  `(lockfree-list-pop-right ,lockfree-list ,default-value))


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
(defun-simple lockfree-list-insert-before (lockfree-list cursor thing)
  (generate-*-insert-before (lockfree-list-insert-before lockfree-list cursor
			     lockfree-list-head
			     lockfree-list-next
			     queue-previous-element
			     queue-next-element
			     read-deleted-queue-node
			     copy-queue-node
			     release-queue-node
			     help-insert-queue-node)
    (create-list-element thing)
    (lockfree-list-insert-after lockfree-list cursor thing)))

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
(defun-simple lockfree-list-insert-after (lockfree-list cursor thing)
  (generate-*-insert-after (lockfree-list-insert-after lockfree-list cursor
			    lockfree-list-tail
			    queue-previous-element
			    queue-next-element
			    read-deleted-queue-node
			    copy-queue-node
			    release-queue-node
			    help-insert-queue-node)
    (create-list-element thing)
    (lockfree-list-insert-before lockfree-list cursor thing)))


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
(defun lockfree-list-delete (cursor &optional lockfree-list)
  (generate-*-delete (cursor lockfree-list)
		     lockfree-list-head
		     lockfree-list-tail
		     queue-next-element
		     queue-previous-element
		     copy-queue-node
		     release-queue-node
		     help-delete-queue-node
		     help-insert-queue-node
		     queue-datum
		     remove-queue-cross-reference
		     lockfree-list-delete))
