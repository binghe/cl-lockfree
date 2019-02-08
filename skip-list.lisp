;;;; Skip List

(in-package :lockfree)

;;; Many popular sequential search structures, such as red-black trees or AVL-
;;; trees, require periodic rebalancing to maintain the structure's logarithmic
;;; depth. Rebalancing works well for sequential tree-based search structures,
;;; but for concurrent structures, rebalancing may cause bottlenecks and
;;; contention. `SKIP LIST' is a proven data structure that provides expected
;;; logarithmic time search without the need to rebalance.

;;; The SkipList is a probabilistic data structure. (No one knows how to provide
;;; this kind of performance without randomization.) Each node is created with a
;;; random top level (topLevel), and belongs to all lists up to that level. Top
;;; levels are chosen so that the expected number of nodes in each level's list
;;; decreases exponentially. Let 0 < p < 1 be the conditional probability that a
;;; node at level i also appears at level i + 1. All nodes appear at level 0.
;;; The probability that a node at level 0 also appears at level i > 0 is p_i.
;;; For example, with p = 1/2, 1/2 of the nodes are expected to appear at level
;;; 1, 1/4 at level 2 and so on, providing a balancing property like the
;;; classical sequential tree-based search structures, except without the need
;;; for complex global restructuring.

;;; Here's a picture of some of the basics for a possible list with 2 levels of
;;; index:

;;;  Head nodes          Index nodes
;;;  +-+    next         +-+                      +-+
;;;  |2|---------------->| |--------------------->| |->null
;;;  +-+                 +-+                      +-+
;;;   |                   |                        |
;;;  +-+    next    +-+  +-+       +-+            +-+       +-+
;;;  |1|----------->| |->| |------>| |----------->| |------>| |->null
;;;  +-+            +-+  +-+       +-+            +-+       +-+
;;;   |              |    |         |              |         |
;;;  +-+  +-+  +-+  +-+  +-+  +-+  +-+  +-+  +-+  +-+  +-+  +-+
;;;  | |->|A|->|B|->|C|->|D|->|E|->|F|->|G|->|H|->|I|->|J|->|K|->null
;;;  +-+  +-+  +-+  +-+  +-+  +-+  +-+  +-+  +-+  +-+  +-+  +-+

;;; We've implemented the Lock-Free Skip List to replace all BINARY-TREEs used
;;; in SymScale G2.                            -- Chun Tian (binghe), May 2014.

(def-structure (skip-list-element
		 (:type vector)
		 (:creations-at-a-time 100)
		 (:constructor
		   make-skip-list-element
		   (skip-list-element-hash-number
		    skip-list-element-key
		    skip-list-element-entry
		    skip-list-element-top-level))
		 (:reclaimer reclaim-skip-list-element-internal))
  skip-list-element-next ; (simple-vector atomic-reference *)
  skip-list-element-hash-number ; fixnum
  skip-list-element-key
  skip-list-element-entry
  skip-list-element-top-level)

(defun-simple reclaim-skip-list-element (element)
  (reclaim-managed-simple-vector-for-skip-list
    (skip-list-element-next element))
  (setf (skip-list-element-next element) nil)
  #+development
  (progn
    (setf (skip-list-element-hash-number element) 0)
    (setf (skip-list-element-key element) nil)
    (setf (skip-list-element-entry element) nil)
    (setf (skip-list-element-top-level element) 0))
  (reclaim-skip-list-element-internal element))

;;; The macro `def-skip-list' defines constructor, reclaimer, clear, and
;;; accessor macros for a named skip list type.

(defmacro skip-list-head (skip-list)
  `(car-of-cons (cdr-of-cons ,skip-list)))

(defmacro skip-list-tail (skip-list)
  `(cdr-of-cons (cdr-of-cons ,skip-list)))

(defmacro skip-list-element-next-0 (skip-list-element)
  `(atomic-reference-object
     (svref (skip-list-element-next ,skip-list-element) 0)))

(defmacro skip-list-element-next-n (skip-list-element level)
  `(atomic-reference-object
     (svref (skip-list-element-next ,skip-list-element) ,level)))

(defmacro def-skip-list (name &key
                              (constructor nil)
                              (reclaimer nil)
                              (clearer nil)
                              (accessor nil)
                              (accessor-given-hash nil)
                              (key-deleter nil)
                              (key-deleter-given-hash nil)
                              (set-if-no-entry-given-hash nil)
                              (hash-function 'sxhashw)
                              (key-comparitor 'eq)
                              (key-reclaimer nil)
                              (entry-reclaimer nil)
                              (flattener nil)
                              (max-level 31))
  (if (not (symbolp name))
      (error "The name argument, ~s, to def-skip-list was not a symbol."
             name))
  (let* ((constructor-name
           (or constructor
               (intern (format nil "MAKE-~a-SKIP-LIST" name))))
         (sentinel-constructor (intern (format nil "MAKE-~a-SKIP-LIST-SENTINEL" name)))
         (reclaimer-name
           (or reclaimer
               (intern (format nil "RECLAIM-~a-SKIP-LIST" name))))
         (clear-name
           (or clearer
               (intern (format nil "CLEAR-~a-SKIP-LIST" name))))
         (element-reclaimer-name (intern (format nil "RECLAIM-~a-NODES" name)))
         (accessor-name (or accessor (intern (format nil "GET-~a" name))))
         (mutator-name (intern (format nil "SET-~a-SKIP-LIST-VALUE" name)))
         (mutator-given-hash
           (if accessor-given-hash
               (intern (format nil "SET-~a" accessor-given-hash))))
         (deleter-name (or key-deleter (intern (format nil "DELETE-~a" name))))
         (flattener-name (or flattener (intern (format nil "FLATTEN-~a" name))))
         (entry-mutator?
           (if (or key-reclaimer entry-reclaimer)
               (intern (format nil "MUTATE-~a-SKIP-LIST-ENTRY" name))
               nil))
         (entry-mutator-var?
           (if entry-mutator?
               (intern (format nil "FP-~a" entry-mutator?))
               nil))
         (skip-list-variable (intern (format nil "~a-SKIP-LIST" name))))
  `(progn

     (defmacro ,constructor-name ()
       (let ((head (make-symbol "HEAD"))
             (tail (make-symbol "TAIL")))
         `(let* ((,tail (,',sentinel-constructor most-positive-fixnum nil))
                 (,head (,',sentinel-constructor most-negative-fixnum ,tail)))
            ;; see macros SKIP-LIST-HEAD & SKIP-LIST-TAIL
            (lookup-cons-macro ',',name (lookup-cons-macro ,head ,tail)))))

     (defun-simple ,sentinel-constructor (hash tail)
       (let ((node (make-skip-list-element hash
					   'sentinel-node
					   (if tail 'head 'tail)
					   ,max-level))
             (next (allocate-managed-simple-vector-for-skip-list ,(1+f max-level))))
         (loop for i from 0 to ,max-level do
           (setf (svref next i) (make-atomic-reference tail)))
         (setf (skip-list-element-next node) next)
         node))

     ,@(when entry-mutator?
         `((defun-void ,entry-mutator? (node new-key new-entry)
             ,@(if key-reclaimer
                   `((,key-reclaimer (skip-list-element-key node)))
                   nil)
             ,@(if entry-reclaimer
                   `((,entry-reclaimer (skip-list-element-entry node)))
                   nil)
             (setf (skip-list-element-key node) new-key)
             (setf (skip-list-element-entry node) new-entry))
           (defparameter ,entry-mutator-var? #',entry-mutator?)))

     ,@(when accessor-given-hash
         `((defmacro ,accessor-given-hash
                     (key ,skip-list-variable hash)
             (if (or (constantp key) (symbolp key))
                 #-development
                 `(lookup-skip-list-entry-macro
                    (cdr ,,skip-list-variable)
                    ,,max-level
                    ,',key-comparitor
                    ,key
                    ,hash)
                 #+development
                 `(lookup-skip-list-entry
                    (cdr ,,skip-list-variable)
                    ,,max-level
                    ',',key-comparitor
                    ,key
                    ,hash)
                 (let ((key-var (gensym)))
                   `(let ((,key-var ,key))
                      #-development
                      (lookup-skip-list-entry-macro
                        (cdr ,,skip-list-variable)
                        ,,max-level
                        ,',key-comparitor
                        ,key-var
                        ,hash)
                      #+development
                      (lookup-skip-list-entry
                        (cdr ,,skip-list-variable)
                        ,,max-level
                        ',',key-comparitor
                        ,key-var
                        ,hash)))))

           (defmacro ,mutator-given-hash
                     (key ,skip-list-variable hash entry)
             (if (or (constantp key) (symbolp key))
                 `(set-skip-list-entry
                    ,,skip-list-variable
                    ,,max-level
                    ',',key-comparitor
                    ,',entry-mutator-var?
                    t ; mutate-old-entry?
                    ,key
                    ,hash
                    ,entry)
                 (let ((key-var (gensym)))
                   `(let ((,key-var ,key))
                      (set-skip-list-entry
                        ,,skip-list-variable
                        ,,max-level
                        ',',key-comparitor
                        ,',entry-mutator-var?
                        t ; mutate-old-entry?
                        ,key-var
                        ,hash
                        ,entry)))))

           (defsetf ,accessor-given-hash ,mutator-given-hash)))

     ,@(when set-if-no-entry-given-hash
         `((defmacro ,set-if-no-entry-given-hash (key ,skip-list-variable hash entry)
             (if (or (constantp key) (symbolp key))
                 `(set-skip-list-entry
                    ,,skip-list-variable
                    ,,max-level
                    ',',key-comparitor
                    nil ; mutator-function?
                    nil ; mutate-old-entry?
                    ,key
                    ,hash
                    ,entry)
                 (let ((key-var (gensym)))
                   `(let ((,key-var ,key))
                      (set-skip-list-entry
                        ,,skip-list-variable
                        ,,max-level
                        ',',key-comparitor
                        nil ; mutator-function?
                        nil ; mutate-old-entry?
                        ,key-var
                        ,hash
                        ,entry)))))))

     (defmacro ,accessor-name (key ,skip-list-variable)
       (if (or (constantp key) (symbolp key))
           #-development
           `(lookup-skip-list-entry-macro
              (cdr ,,skip-list-variable)
              ,,max-level
              ,',key-comparitor
              ,key
              (,',hash-function ,key))
           #+development
           `(lookup-skip-list-entry
              (cdr ,,skip-list-variable)
              ,,max-level
              ',',key-comparitor
              ,key
              (,',hash-function ,key))
           (let ((key-evaled (gensym)))
             `(let ((,key-evaled ,key))
                #-development
                (lookup-skip-list-entry-macro
                  (cdr ,,skip-list-variable)
                  ,,max-level
                  ,',key-comparitor
                  ,key-evaled
                  (,',hash-function ,key-evaled))
                #+development
                (lookup-skip-list-entry
                  (cdr ,,skip-list-variable)
                  ,,max-level
                  ',',key-comparitor
                  ,key-evaled
                  (,',hash-function ,key-evaled))))))

     (defmacro ,mutator-name (key ,skip-list-variable entry)
       (let ((key-evaled (gensym)))
         `(let ((,key-evaled ,key))
            (set-skip-list-entry
              ,,skip-list-variable
              ,,max-level
              ',',key-comparitor
              ,',entry-mutator-var?
              t ; mutate-old-entry?
              ,key-evaled
              (,',hash-function ,key-evaled)
              ,entry))))

     (defsetf ,accessor-name ,mutator-name)

     (defmacro ,deleter-name (key ,skip-list-variable)
       ,(if (and (null key-reclaimer) (null entry-reclaimer))
            `(if (or (symbolp key) (constantp key))
                 `(progn
                    (delete-skip-list-entry
                      #',',key-comparitor
                      ,key
                      ,,skip-list-variable
                      ,,max-level
                      (,',hash-function ,key))
                    nil)
                 (let ((key-evaled (gensym)))
                   `(let ((,key-evaled ,key))
                      (delete-skip-list-entry
                        #',',key-comparitor
                        ,key-evaled
                        ,,skip-list-variable
                        ,,max-level
                        (,',hash-function ,key-evaled))
                      nil)))
            ``(multiple-value-bind (old-key old-entry)
                  ,(if (or (symbolp key) (constantp key))
                       `(delete-skip-list-entry
                          #',',key-comparitor
                          ,key
                          ,,skip-list-variable
                          ,,max-level
                          (,',hash-function ,key))
                       (let ((key-evaled (gensym)))
                         `(let ((,key-evaled ,key))
                            (delete-skip-list-entry
                              #',',key-comparitor
                              ,key-evaled
                              ,,skip-list-variable
                              ,,max-level
                              (,',hash-function ,key-evaled)))))
                ,@',(cond ((null key-reclaimer)
                           `((declare (ignore old-key))
                             (when old-entry (,entry-reclaimer old-entry))))
                          ((null entry-reclaimer)
                           `((declare (ignore old-entry))
                             (when old-key (,key-reclaimer old-key))))
                          (t
                           `((when old-key (,key-reclaimer old-key))
                             (when old-entry (,entry-reclaimer old-entry)))))
                nil)))

     ,@(if key-deleter-given-hash
           `((defmacro ,key-deleter-given-hash
                        (key ,skip-list-variable key-hash)
               ,(if (and (null key-reclaimer) (null entry-reclaimer))
                    ``(progn
                        (delete-skip-list-entry
                          #',',key-comparitor
                          ,key
                          ,,skip-list-variable
                          ,,max-level
                          ,key-hash)
                        nil)
                    ``(multiple-value-bind (old-key old-entry)
                          (delete-skip-list-entry
                            #',',key-comparitor
                            ,key
                            ,,skip-list-variable
                            ,,max-level
                            ,key-hash)
                        ,@',(cond ((null key-reclaimer)
                                   `((declare (ignore old-key))
                                     (when old-entry (,entry-reclaimer old-entry))))
                                  ((null entry-reclaimer)
                                   `((declare (ignore old-entry))
                                     (when old-key (,key-reclaimer old-key))))
                                  (t
                                   `((when old-key (,key-reclaimer old-key))
                                     (when old-entry (,entry-reclaimer old-entry)))))
                        nil)))))

     ,@(unless (or key-reclaimer entry-reclaimer)
	 `((defun-simple ,element-reclaimer-name (,skip-list-variable tail)
	     (loop until (eq ,skip-list-variable tail)
		   for next-element = (skip-list-element-next-0 ,skip-list-variable)
		   for key = (skip-list-element-key ,skip-list-variable)
		   for entry = (skip-list-element-entry ,skip-list-variable)
		   do
	       (reclaim-skip-list-element ,skip-list-variable)
	       ,@(when key-reclaimer
		   `((,key-reclaimer key)))
	       ,@(when entry-reclaimer
		   `((,entry-reclaimer entry)))
               (setq ,skip-list-variable next-element)))))

     ;; Note that the reclaimer and clearing functions delete a tree by
     ;; repeatedly deleting the first key in the root element of the tree when
     ;; there are reclaimers for either the key or the entry.  This is done
     ;; since the reclaimers for the keys or entries may further mutate this
     ;; binary tree, rebalancing it in the process.  The old reclaimers
     ;; experienced bugs in rules because of this.

     (def-substitution-macro ,reclaimer-name (,skip-list-variable)
       (progn
         ,(if (or key-reclaimer entry-reclaimer)
            `(loop with head = (skip-list-head ,skip-list-variable)
                   with tail = (skip-list-tail ,skip-list-variable)
                   for element? = (skip-list-element-next-0 head)
                   for key? = (skip-list-element-key element?)
                   while (neq element? tail)
                   do
               (,deleter-name key? ,skip-list-variable)
                   finally
                     (reclaim-skip-list-element head)
                     (reclaim-skip-list-element tail)
                     (setf (cddr ,skip-list-variable) nil)
                     (setf (cadr ,skip-list-variable) nil)
                     (setf (car ,skip-list-variable) nil)
                     (reclaim-lookup-list-macro ,skip-list-variable))
            `(let* ((head (skip-list-head ,skip-list-variable))
                    (tail (skip-list-tail ,skip-list-variable))
                    (element? (skip-list-element-next-0 head)))
               (when (neq element? tail)
                 (,element-reclaimer-name element? tail))
               (reclaim-skip-list-element head)
               (reclaim-skip-list-element tail)
               (setf (cddr ,skip-list-variable) nil)
               (setf (cadr ,skip-list-variable) nil)
               (setf (car ,skip-list-variable) nil)
               (reclaim-lookup-list-macro ,skip-list-variable)))))

     (defun-simple ,clear-name (,skip-list-variable)
       ,(if (or key-reclaimer entry-reclaimer)
            `(loop with head = (skip-list-head ,skip-list-variable)
                   with tail = (skip-list-tail ,skip-list-variable)
                   for element? = (skip-list-element-next-0 head)
                   for key? = (skip-list-element-key element?)
                   while (neq element? tail)
                   do
               (,deleter-name key? ,skip-list-variable))
            `(let* ((head (skip-list-head ,skip-list-variable))
                    (tail (skip-list-tail ,skip-list-variable))
                    (element? (skip-list-element-next-0 head)))
               (when (neq element? tail)
                 (,element-reclaimer-name element? tail))))
       ,skip-list-variable)

     (defmacro ,flattener-name (,skip-list-variable)
       `(flatten-skip-list (cdr ,,skip-list-variable)))

     ',name)))

(defun flatten-skip-list (skip-list)
  (gensym-dstruct-bind ((head . tail) skip-list)
    (loop for node = (skip-list-element-next-0 head)
                   then (skip-list-element-next-0 node)
          until (eq node tail)
          collect (early-eval-cons
                    (skip-list-element-key node)
                    (skip-list-element-entry node))
          using early-eval-cons)))

(declare-side-effect-free-function lookup-skip-list-entry)

#+SymScale
(defun-simple lookup-skip-list-entry (skip-list-element max-level key-comparitor key key-hash)
  (declare (type fixnum key-hash max-level))
  (let ((bottom-level 0)
        (marked nil)
        (pred (car-of-cons skip-list-element)) ; head
        (curr nil)
        (succ nil))
    (loop for level from max-level downto bottom-level do
      (setq curr (skip-list-element-next-n pred level))
      (loop
        (multiple-value-setq (succ marked)
            (get-atomic-reference (svref (skip-list-element-next curr) level)))
        (loop while marked do
          (setq curr (skip-list-element-next-n pred level))
          (multiple-value-setq (succ marked)
              (get-atomic-reference (svref (skip-list-element-next curr) level))))
	(let ((entry-hash (skip-list-element-hash-number curr)))
	  (if (or (<f entry-hash key-hash)
		  (and (=f entry-hash key-hash)
		       (not
			 (let ((entry-key (skip-list-element-key curr)))
			   (cond ((eq key-comparitor 'equal)
				  (equal key entry-key))
				 ((eq key-comparitor 'string=)
				  (string= key entry-key))
				 ((eq key-comparitor 'equal-rule-context)
				  (equal-rule-context key entry-key))
				 (t
				  (funcall key-comparitor key entry-key)))))))
	      (setq pred curr
		    curr succ)
	    (return)))))
    (when (=f (skip-list-element-hash-number curr) key-hash)
      (let ((entry-key (skip-list-element-key curr)))
        (when (cond ((eq key-comparitor 'equal)
                     (equal key entry-key))
                    ((eq key-comparitor 'string=)
                     (string= key entry-key))
                    ((eq key-comparitor 'equal-rule-context)
                     (equal-rule-context key entry-key))
                    (t
                     (funcall key-comparitor key entry-key)))
          (skip-list-element-entry curr))))))

#-SymScale
(defun-simple lookup-skip-list-entry (skip-list-element max-level key-comparitor key key-hash)
  (declare (type fixnum key-hash max-level))
  (let ((bottom-level 0)
        (pred (car-of-cons skip-list-element)) ; head
        (curr nil))
    (loop for level from max-level downto bottom-level do
      (setq curr (skip-list-element-next-n pred level))
      (loop as entry-hash = (skip-list-element-hash-number curr)
	    do
	(if (or (<f entry-hash key-hash)
		(and (=f entry-hash key-hash)
		     (not
		       (let ((entry-key (skip-list-element-key curr)))
			 (cond ((eq key-comparitor 'equal)
				(equal key entry-key))
			       ((eq key-comparitor 'string=)
				(string= key entry-key))
			       ((eq key-comparitor 'equal-rule-context)
				(equal-rule-context key entry-key))
			       (t
				(funcall key-comparitor key entry-key)))))))
	    (setq pred curr
		  curr (skip-list-element-next-n curr level))
	  (return))))
    (when (=f (skip-list-element-hash-number curr) key-hash)
      (let ((entry-key (skip-list-element-key curr)))
        (when (cond ((eq key-comparitor 'equal)
                     (equal key entry-key))
                    ((eq key-comparitor 'string=)
                     (string= key entry-key))
                    ((eq key-comparitor 'equal-rule-context)
                     (equal-rule-context key entry-key))
                    (t
                     (funcall key-comparitor key entry-key)))
          (skip-list-element-entry curr))))))

#+SymScale
(defmacro lookup-skip-list-entry-macro (skip-list-element max-level key-comparitor key key-hash)
  (let ((skip-list (make-symbol "SKIP-LIST"))
        (key-value (make-symbol "KEY-VALUE"))
        (key-hash-value (make-symbol "KEY-HASH-VALUE"))
        (entry-hash (make-symbol "ENTRY-HASH"))
        (bottom-level (make-symbol "BOTTOM-LEVEL"))
        (level (make-symbol "LEVEL"))
        (marked (make-symbol "MARKED"))
        (pred (make-symbol "PRED"))
        (curr (make-symbol "CURR"))
        (succ (make-symbol "SUCC")))
    `(let* ((,skip-list ,skip-list-element)
            (,key-value ,key)
            (,key-hash-value ,key-hash)
            (,bottom-level 0)
            (,marked nil)
            (,pred (car-of-cons ,skip-list))
            (,curr nil)
            (,succ nil))
       (declare (type fixnum ,key-hash-value))
       (loop for ,level from ,max-level downto ,bottom-level do
         (setq ,curr (skip-list-element-next-n ,pred ,level))
         (loop
           (multiple-value-setq (,succ ,marked)
             (get-atomic-reference (svref (skip-list-element-next ,curr) ,level)))
           (loop while ,marked do
             (setq ,curr (skip-list-element-next-n ,pred ,level))
             (multiple-value-setq (,succ ,marked)
               (get-atomic-reference (svref (skip-list-element-next ,curr) ,level))))
	   (let ((,entry-hash (skip-list-element-hash-number ,curr)))
	     (if (or (<f ,entry-hash ,key-hash-value)
		     (and (=f ,entry-hash ,key-hash-value)
			  (not (,key-comparitor ,key-value (skip-list-element-key ,curr)))))
		 (setq ,pred ,curr
		       ,curr ,succ)
	       (return)))))
       (when (=f (skip-list-element-hash-number ,curr) ,key-hash-value)
	 (when (,key-comparitor ,key-value (skip-list-element-key ,curr))
	   (skip-list-element-entry ,curr))))))

#-SymScale
(defmacro lookup-skip-list-entry-macro (skip-list-element max-level key-comparitor key key-hash)
  (let ((skip-list (make-symbol "SKIP-LIST"))
        (key-value (make-symbol "KEY-VALUE"))
        (key-hash-value (make-symbol "KEY-HASH-VALUE"))
        (entry-hash (make-symbol "ENTRY-HASH"))
        (bottom-level (make-symbol "BOTTOM-LEVEL"))
        (level (make-symbol "LEVEL"))
        (pred (make-symbol "PRED"))
        (curr (make-symbol "CURR")))
    `(let* ((,skip-list ,skip-list-element)
            (,key-value ,key)
            (,key-hash-value ,key-hash)
            (,bottom-level 0)
            (,pred (car-of-cons ,skip-list))
            (,curr nil))
       (declare (type fixnum ,key-hash-value))
       (loop for ,level from ,max-level downto ,bottom-level do
         (setq ,curr (skip-list-element-next-n ,pred ,level))
         (loop as ,entry-hash = (skip-list-element-hash-number ,curr)
	       do
	   (if (or (<f ,entry-hash ,key-hash-value)
		   (and (=f ,entry-hash ,key-hash-value)
			(not (,key-comparitor ,key-value (skip-list-element-key ,curr)))))
	       (setq ,pred ,curr
		     ,curr (skip-list-element-next-n ,curr ,level))
	     (return))))
       (when (=f (skip-list-element-hash-number ,curr) ,key-hash-value)
	 (when (,key-comparitor ,key-value (skip-list-element-key ,curr))
	   (skip-list-element-entry ,curr))))))

(defmacro make-skip-list-node (hash key entry height)
  (let ((node (make-symbol "NODE"))
        (next (make-symbol "NEXT")))
    `(let* ((,node (make-skip-list-element ,hash ,key ,entry ,height))
            (,next (allocate-managed-simple-vector-for-skip-list (1+f ,height))))
       (setf (skip-list-element-next ,node) ,next)
       ,node)))

(defconstant half-of-most-positive-fixnum (floorf most-positive-fixnum 2))

(defun-simple random-level (max-level)
  (declare (type fixnum max-level))
  (loop with level = 0
        while (and (<f (*f 2 (current-system-case
                               (ab #+development (random half-of-most-positive-fixnum)
                                   #-development (g2-random half-of-most-positive-fixnum))
                               (t (random half-of-most-positive-fixnum))))
                       half-of-most-positive-fixnum)
                   (<f level max-level))
        do (incff level)
        finally (return level)))

(defconstant skip-list-global-max-level 32)
(defvar skip-list-find-preds (make-array skip-list-global-max-level))
(defvar skip-list-find-succs (make-array skip-list-global-max-level))

#+SymScale
(defun-simple skip-list-find (skip-list max-level key-comparitor key hash preds succs)
  (let ((bottom-level 0)
        marked snip
        pred curr succ)
    (tagbody retry
      (loop
        (setq pred skip-list)
        (loop for level from max-level downto bottom-level do
          (setq curr (skip-list-element-next-n pred level))
          (loop for next = (skip-list-element-next curr)
		do
            (multiple-value-setq (succ marked)
              (get-atomic-reference (svref next level)))
            (loop while marked do
              (setq snip (compare-and-swap (svref (skip-list-element-next pred) level)
                                           (make-atomic-reference curr)
                                           (make-atomic-reference succ)))
              (unless snip (go retry))
              (setq curr (skip-list-element-next-n pred level))
              (multiple-value-setq (succ marked)
                (get-atomic-reference (svref (skip-list-element-next curr) level))))
	    (let ((entry-hash (skip-list-element-hash-number curr)))
	      (if (or (<f entry-hash hash)
		      ;; this only happens at bottom level
		      (and (=f entry-hash hash)
			   (not
			     (let ((entry-key (skip-list-element-key curr)))
			       (cond ((eq key-comparitor 'equal)
				      (equal key entry-key))
				     ((eq key-comparitor 'string=)
				      (string= key entry-key))
				     ((eq key-comparitor 'equal-rule-context)
				      (equal-rule-context key entry-key))
				     (t
				      (funcall key-comparitor key entry-key)))))))
		  (setq pred curr
			curr succ)
		(return))))
          (setf (svref preds level) pred
                (svref succs level) curr))
        (return-from skip-list-find
          (when (and (=f (skip-list-element-hash-number curr) hash)
		     (let ((entry-key (skip-list-element-key curr)))
		       (cond ((eq key-comparitor 'equal)
			      (equal key entry-key))
			     ((eq key-comparitor 'string=)
			      (string= key entry-key))
			     ((eq key-comparitor 'equal-rule-context)
			      (equal-rule-context key entry-key))
			     (t
			      (funcall key-comparitor key entry-key)))))
            curr)))))) ; return current node

#-SymScale
(defun-simple skip-list-find (skip-list max-level key-comparitor key hash preds succs)
  (let ((bottom-level 0)
	(pred skip-list)
	curr)
    (loop for level from max-level downto bottom-level do
      (setq curr (skip-list-element-next-n pred level))
      (loop as entry-hash = (skip-list-element-hash-number curr)
	    do
	(if (or (<f entry-hash hash)
		;; this only happens at bottom level
		(and (=f entry-hash hash)
		     (not
		       (let ((entry-key (skip-list-element-key curr)))
			 (cond ((eq key-comparitor 'equal)
				(equal key entry-key))
			       ((eq key-comparitor 'string=)
				(string= key entry-key))
			       ((eq key-comparitor 'equal-rule-context)
				(equal-rule-context key entry-key))
			       (t
				(funcall key-comparitor key entry-key)))))))
	    (setq pred curr
		  curr (skip-list-element-next-n curr level))
	  (return)))
      (setf (svref preds level) pred
	    (svref succs level) curr))
    (when (and (=f (skip-list-element-hash-number curr) hash)
	       (let ((entry-key (skip-list-element-key curr)))
		       (cond ((eq key-comparitor 'equal)
			      (equal key entry-key))
			     ((eq key-comparitor 'string=)
			      (string= key entry-key))
			     ((eq key-comparitor 'equal-rule-context)
			      (equal-rule-context key entry-key))
			     (t
			      (funcall key-comparitor key entry-key)))))
      curr)))

#+SymScale
(defun-simple set-skip-list-entry
       (skip-list max-level key-comparitor mutator-function? mutate-old-entry?
	key key-hash entry)
  (declare (type fixnum key-hash max-level))
  (let* ((bottom-level 0)
	 (head (skip-list-head skip-list))
	 (preds skip-list-find-preds)
	 (succs skip-list-find-succs))
    (loop as insertion-point
	     = (skip-list-find head max-level key-comparitor key key-hash preds succs)
	  do
      (when insertion-point
	(if mutate-old-entry?
	    (if mutator-function?
		(funcall-simple-compiled-function
		  mutator-function? insertion-point key entry)
	      (progn
		(setf (skip-list-element-key insertion-point) key)
		(setf (skip-list-element-entry insertion-point) entry)))
	  (setq entry (skip-list-element-entry insertion-point)))
	(return-from set-skip-list-entry entry))
      (let* ((pred (svref preds bottom-level))
	     (top-level (if (=f (skip-list-element-hash-number pred) key-hash)
			    ;; if the hash is duplicated with previous node, the level is:
			    (skip-list-element-top-level pred)
			  (random-level max-level)))
	     (new-node (make-skip-list-node key-hash key entry top-level)))
	(loop for level from bottom-level to top-level do
	  (setf (svref (skip-list-element-next new-node) level)
		(make-atomic-reference (svref succs level))))
	(let ((succ (svref succs bottom-level)))
	  (if (compare-and-swap (svref (skip-list-element-next pred) bottom-level)
				(make-atomic-reference succ)
				(make-atomic-reference new-node))
	      (progn
		(loop for level from (1+f bottom-level) to top-level do
		  (loop
		    (setq pred (svref preds level)
			  succ (svref succs level))
		    (when (compare-and-swap (svref (skip-list-element-next pred) level)
					    (make-atomic-reference succ)
					    (make-atomic-reference new-node))
		      (return nil))
		    (skip-list-find head max-level key-comparitor key key-hash preds succs)))
		(return-from set-skip-list-entry entry))
	    ;; Failed CAS means previous node is not pred any more, need to reclaim
	    ;; the new node and go over the whole process again.
	    (progn
	      (reclaim-skip-list-element new-node))))))))

#-SymScale
(defun-simple set-skip-list-entry
       (skip-list max-level key-comparitor mutator-function? mutate-old-entry?
	key key-hash entry)
  (declare (type fixnum key-hash max-level))
  (let* ((bottom-level 0)
	 (head (skip-list-head skip-list))
	 (preds skip-list-find-preds)
	 (succs skip-list-find-succs)
	 (insertion-point
	  (skip-list-find head max-level key-comparitor key key-hash preds succs)))
    (if insertion-point
	(if mutate-old-entry?
	    (if mutator-function?
		(funcall-simple-compiled-function
		  mutator-function? insertion-point key entry)
	      (progn
		(setf (skip-list-element-key insertion-point) key)
		(setf (skip-list-element-entry insertion-point) entry)))
	  (setq entry (skip-list-element-entry insertion-point)))
      (let* ((pred-0 (svref preds bottom-level))
	     (top-level (if (=f (skip-list-element-hash-number pred-0) key-hash)
			    ;; if the hash is duplicated with previous node
			    (skip-list-element-top-level pred-0)
			  (random-level max-level)))
	     (new-node (make-skip-list-node key-hash key entry top-level)))
	(loop for level from bottom-level to top-level
	      for succ = (svref succs level)
	      for pred = (svref preds level)
	      do
	  (setf (svref (skip-list-element-next new-node) level) succ)
	  (setf (svref (skip-list-element-next pred) level) new-node))))
    entry))

;; TODO: there must be bugs in this function. --binghe
#+SymScale
(defun delete-skip-list-entry (comparitor key skip-list max-level key-hash)
  (declare (type fixnum max-level key-hash))
  (let* ((bottom-level 0)
	 (head (skip-list-head skip-list))
	 (preds skip-list-find-preds)
	 (succs skip-list-find-succs))
    ;; note: there's no LOOP in single-thread version
    (loop as deletion-point
	     = (skip-list-find head max-level comparitor key key-hash preds succs)
	  doing
      (when (null deletion-point)
	(return-from delete-skip-list-entry (values nil nil)))

      (let ((node-to-remove (svref succs bottom-level))
	    (old-key (skip-list-element-key deletion-point))
	    (old-entry (skip-list-element-entry deletion-point))
            succ marked)
	#+development
	(unless (eq node-to-remove deletion-point)
	  (error "node-to-remove <> deletion-point ?!"))
        (loop for level from (skip-list-element-top-level node-to-remove)
                        downto (1+f bottom-level)
              do
          (multiple-value-setq (succ marked)
            (get-atomic-reference (svref (skip-list-element-next node-to-remove) level)))
          (loop while (not marked) do
            (compare-and-swap (svref (skip-list-element-next node-to-remove) level)
                              (make-atomic-reference succ nil)
                              (make-atomic-reference succ t))
            (multiple-value-setq (succ marked)
              (get-atomic-reference
                (svref (skip-list-element-next node-to-remove) level)))))
        (multiple-value-setq (succ marked)
          (get-atomic-reference
            (svref (skip-list-element-next node-to-remove) bottom-level)))
        (loop as i-marked-it =
              (compare-and-swap (svref (skip-list-element-next node-to-remove) bottom-level)
                                (make-atomic-reference succ nil)
                                (make-atomic-reference succ t))
              do
           (multiple-value-setq (succ marked)
             (get-atomic-reference (svref (skip-list-element-next (svref succs bottom-level))
                                          bottom-level)))
           (cond (i-marked-it
                  (skip-list-find head max-level comparitor key key-hash preds succs)
                  (return-from delete-skip-list-entry
                    (values old-key old-entry)))
                 (marked
                  ;; other threads has removed it first
                  (return-from delete-skip-list-entry
                    (values old-key old-entry)))))))))

#-SymScale
(defun delete-skip-list-entry (comparitor key skip-list max-level key-hash)
  (declare (type fixnum max-level key-hash))
  (let* ((bottom-level 0)
	 (head (skip-list-head skip-list))
	 (preds skip-list-find-preds)
	 (succs skip-list-find-succs)
	 (deletion-point
	   (skip-list-find head max-level comparitor key key-hash preds succs)))
    ;; return directly if didn't found the node.
    (when (null deletion-point)
      (return-from delete-skip-list-entry (values nil nil)))

    (let ((node-to-remove deletion-point)
	  (old-key (skip-list-element-key deletion-point))
	  (old-entry (skip-list-element-entry deletion-point)))
      ;; delete the node in the deletion-point variable.
      (loop for level from (skip-list-element-top-level node-to-remove)
		      downto bottom-level
	    for pred = (svref preds level)
	    doing
	(when (eq (skip-list-element-next-n pred level) node-to-remove)
	  (setf (svref (skip-list-element-next pred) level)
		(skip-list-element-next-n node-to-remove level))))

      ;; reclaim node element.
      (reclaim-skip-list-element node-to-remove)
      (values old-key old-entry))))

(defmacro skip-list-empty-p (skip-list)
  (let ((temp (gensym)))
    `(let ((,temp (cdr-of-cons ,skip-list)))
       (eq (skip-list-element-next-0 (car-of-cons ,temp))
           (cdr-of-cons ,temp)))))

(defmacro skip-list-p (thing)
  (let ((temp (gensym)))
    `(let ((,temp (cdr ,thing))) ; using CDR to allow thing to be NIL
       (and (consp ,temp)
            (simple-vector-p (car-of-cons ,temp))
            (simple-vector-p (cdr-of-cons ,temp))))))

(def-substitution-macro skip-list-or-binary-tree-empty-p (thing)
  (if (skip-list-p thing)
      (skip-list-empty-p thing)
    (binary-tree-empty-p thing)))

(define-loop-path skip-list-value
  expand-skip-list-or-binary-tree-value-loop-iterator (of))

(defun-for-macro expand-skip-list-or-binary-tree-value-loop-iterator
                 (method-name
                   iter-var iter-var-data-type prep-phrases inclusive?
                   allowed-preps method-specific-data)
  (declare (ignore method-name allowed-preps method-specific-data))
  (when inclusive?
    (error "The skip-list-or-binary-tree-value iteration path does not support ~
inclusive iterations."))
  (let* ((skip-list-or-binary-tree-form-entry (assq 'of prep-phrases))
         (skip-list-or-binary-tree-form (second skip-list-or-binary-tree-form-entry))
         (skip-list-form (loop-gentemp 'skip-list-form-))
         (binary-tree-form (loop-gentemp 'binary-tree-form-))
         (skip-list-p (loop-gentemp 'skip-list-p-))
         (node-stack (loop-gentemp 'node-stack-))
         (current-node (loop-gentemp 'current-node-))
         (next-node? (loop-gentemp 'next-node-))
         (tail-node (loop-gentemp 'tail-node-))
         (current-alist (loop-gentemp 'current-alist-))
         (entry-cons (loop-gentemp 'entry-cons-))
         (less-than-branch? (loop-gentemp 'less-than-branch?-))
         init-bindings
         prologue-forms
         (pre-step-tests nil)
         (steppings nil)
         post-step-tests
         post-step-settings)
    (when (null skip-list-or-binary-tree-form-entry)
      (error "The skip-list-or-binary-tree-value iteration path requires an ~
\"OF skip-list-or-binary-tree-form\"."))
    (when (or (not (symbolp iter-var)) (eq iter-var-data-type t))
      (setq iter-var-data-type nil))

    (setq init-bindings
          `((scope-conses scope-conses)
            (,node-stack nil)
            (,current-node nil)
            (,skip-list-form ,skip-list-or-binary-tree-form)
            (,binary-tree-form ,skip-list-or-binary-tree-form)
            (,skip-list-p (skip-list-p ,skip-list-or-binary-tree-form))
            (,next-node? nil)
            (,tail-node nil) 
            (,current-alist nil)
            (,entry-cons nil)
            ,(if iter-var-data-type
                 `(,iter-var nil ,iter-var-data-type)
                 `(,iter-var))))

    (setq prologue-forms
          `((cond (,skip-list-p
		   (setq ,next-node?
			 (skip-list-element-next-0 (skip-list-head ,skip-list-form))
			 ,tail-node
			 (skip-list-tail ,skip-list-form))
		   (when (eq ,next-node? ,tail-node)
		     (setq ,next-node? nil)))
		  (t ; binary-tree
		   (setq ,next-node? (cdr-of-cons ,binary-tree-form))))))

    (setq post-step-tests
          `(progn
             (cond
               (,current-alist
                (setq ,entry-cons (car-of-cons ,current-alist))
                (setq ,current-alist (cdr-of-cons ,current-alist)))
               (,skip-list-p
		(cond (,next-node?
		       (setq ,current-node ,next-node?)
		       (setq ,next-node? (skip-list-element-next-0 ,current-node))
		       (when (eq ,next-node? ,tail-node)
			 (setq ,next-node? nil))
		       (setq ,entry-cons
			     (scope-cons (skip-list-element-key ,current-node)
					 (skip-list-element-entry ,current-node))))
		      (t
		       (setq ,current-node nil))))
               (t
                (cond
                  (,next-node?
                   (setq ,current-node ,next-node?)
                   (loop for ,less-than-branch? = (less-than-branch
                                                    ,current-node)
                         while ,less-than-branch?
                         do
                     (setq ,node-stack (scope-cons ,current-node ,node-stack))
                     (setq ,current-node ,less-than-branch?)))
                  (,node-stack
                   (setq ,next-node? ,node-stack)
                   (setq ,current-node (car-of-cons ,node-stack))
                   (setq ,node-stack (cdr-of-cons ,node-stack)))
                  (t
                   (setq ,current-node nil)))
                (when ,current-node
                  (setq ,next-node? (greater-than-branch ,current-node))
                  (setq ,current-alist (binary-element-alist ,current-node))
                  (setq ,entry-cons (car-of-cons ,current-alist))
                  (setq ,current-alist (cdr-of-cons ,current-alist)))))
	     (null ,current-node)))

    ;; skip-list-entry-cons is different only in this part.
    (if (and (symbolp iter-var)
             iter-var-data-type
             (neq iter-var-data-type t))
        (setq post-step-settings
              `(,iter-var (the ,iter-var-data-type (cdr-of-cons ,entry-cons))))
        (setq post-step-settings
              `(,iter-var (cdr-of-cons ,entry-cons))))

    `(,init-bindings
      ,prologue-forms
      ,pre-step-tests
      ,steppings
      ,post-step-tests
      ,post-step-settings)))

(define-loop-path skip-list-entry-cons
  expand-skip-list-or-binary-tree-entry-cons-loop-iterator (of))

(defun-for-macro expand-skip-list-or-binary-tree-entry-cons-loop-iterator
                 (method-name
                   iter-var iter-var-data-type prep-phrases inclusive?
                   allowed-preps method-specific-data)
  (declare (ignorable method-name allowed-preps iter-var-data-type method-specific-data))
  (when inclusive?
    (error "The skip-list-or-binary-tree-value iteration path does not support ~
inclusive iterations."))
  (let* ((skip-list-or-binary-tree-form-entry (assq 'of prep-phrases))
         (skip-list-or-binary-tree-form (second skip-list-or-binary-tree-form-entry))
         (skip-list-form (loop-gentemp 'skip-list-form-))
         (binary-tree-form (loop-gentemp 'binary-tree-form-))
         (skip-list-p (loop-gentemp 'skip-list-p-))
         (node-stack (loop-gentemp 'node-stack-))
         (current-node (loop-gentemp 'current-node-))
         (next-node? (loop-gentemp 'next-node-))
         (tail-node (loop-gentemp 'tail-node-))
         (current-alist (loop-gentemp 'current-alist-))
         (entry-cons (loop-gentemp 'entry-cons-))
         (less-than-branch? (loop-gentemp 'less-than-branch?-))
         init-bindings
         prologue-forms
         (pre-step-tests nil)
         (steppings nil)
         post-step-tests
         post-step-settings)
    (when (null skip-list-or-binary-tree-form-entry)
      (error "The skip-list-or-binary-tree-value iteration path requires an ~
\"OF skip-list-or-binary-tree-form\"."))

    (setq init-bindings
          `((scope-conses scope-conses)
            (,node-stack nil)
            (,current-node nil)
            (,skip-list-form ,skip-list-or-binary-tree-form)
            (,binary-tree-form ,skip-list-or-binary-tree-form)
            (,skip-list-p (skip-list-p ,skip-list-or-binary-tree-form))
            (,next-node? nil)
            (,tail-node nil) 
            (,current-alist nil)
            (,entry-cons nil)
            (,iter-var)))

    (setq prologue-forms
          `((cond (,skip-list-p
		   (setq ,next-node?
			 (skip-list-element-next-0 (skip-list-head ,skip-list-form))
			 ,tail-node
			 (skip-list-tail ,skip-list-form))
		   (when (eq ,next-node? ,tail-node)
		     (setq ,next-node? nil)))
		  (t ; binary-tree
		   (setq ,next-node? (cdr-of-cons ,binary-tree-form))))))

    (setq post-step-tests
          `(progn
             (cond
               (,current-alist
                (setq ,entry-cons (car-of-cons ,current-alist))
                (setq ,current-alist (cdr-of-cons ,current-alist)))
               (,skip-list-p
		(cond (,next-node?
		       (setq ,current-node ,next-node?)
		       (setq ,next-node? (skip-list-element-next-0 ,current-node))
		       (when (eq ,next-node? ,tail-node)
			 (setq ,next-node? nil))
		       (setq ,entry-cons
			     (scope-cons (skip-list-element-key ,current-node)
					 (skip-list-element-entry ,current-node))))
		      (t
		       (setq ,current-node nil))))
               (t
                (cond
                  (,next-node?
                   (setq ,current-node ,next-node?)
                   (loop for ,less-than-branch? = (less-than-branch
                                                    ,current-node)
                         while ,less-than-branch?
                         do
                     (setq ,node-stack (scope-cons ,current-node ,node-stack))
                     (setq ,current-node ,less-than-branch?)))
                  (,node-stack
                   (setq ,next-node? ,node-stack)
                   (setq ,current-node (car-of-cons ,node-stack))
                   (setq ,node-stack (cdr-of-cons ,node-stack)))
                  (t
                   (setq ,current-node nil)))
                (when ,current-node
                  (setq ,next-node? (greater-than-branch ,current-node))
                  (setq ,current-alist (binary-element-alist ,current-node))
                  (setq ,entry-cons (car-of-cons ,current-alist))
                  (setq ,current-alist (cdr-of-cons ,current-alist)))))
	     (null ,current-node)))

    (setq post-step-settings
          `(,iter-var ,entry-cons))

    ;; Return a list of the six path elements.
    `(,init-bindings
      ,prologue-forms
      ,pre-step-tests
      ,steppings
      ,post-step-tests
      ,post-step-settings)))

;; Skip list pretty printer, it assumes single char keys for showing up pretty.
#+development
(defun describe-skip-list (skip-list)
  (let ((head (skip-list-head skip-list))
        (tail (skip-list-tail skip-list))
        (level-list nil)
        (max-level 0)
        (element-list nil)
        (n-element 0)
        (print-limit 26))
    ;; get level 0 element first
    (loop for node = (skip-list-element-next-0 head)
                then (skip-list-element-next-0 node)
          until (eq node tail)
          maximize (skip-list-element-top-level node) into m
          finally (setq max-level m)
          do
      (push (skip-list-element-top-level node) level-list)
      (push (skip-list-element-key node) element-list)
      (incf n-element))
    (setq level-list (nreverse level-list))
    (setq element-list (nreverse element-list))
    (unless level-list
      (format t ";;;  Skip-list is empty.~%")
      (return-from describe-skip-list))
    ;; title
    (format t ";;;  Head nodes")
    (loop with node = head
          with done = nil
          for j on level-list
          for n = 1 then (1+ n)
          until (or (eq node tail) (> n print-limit))
          finally (unless done (terpri))
          do
      (cond ((=f n 1)
             nil)      ; "nodes", no spaces
            ((=f n 2)
             (format t "     ")) ; no spaces
            ((=f (car j) max-level)
             (format t "Index nodes~%")
             (setq done t)
             (return))
            (t (format t "     "))))
    ;; body
    (loop for i from max-level downto 0 do
      ;; 1st round:
      (if (<f i 10)
          (format t ";;;  +-+  ")
          (format t ";;;  +--+ "))
      (loop with node = head
            with nex-p = nil
            for j on level-list
            for n = 1 then (1+f n)
            until (or (eq node tail) (>f n print-limit))
            do
        (if (>=f (car j) i)
            (progn
              (setq node (skip-list-element-next-n node i))
              (format t "+-+  "))
          (cond ((and (=f n 1) (<f (or (cadr j) most-positive-fixnum) i))
                 (format t "  nex")
                 (setq nex-p t))
                ((and (=f n 2) nex-p)
                 (format t "t    "))
                (t
                 (format t "     ")))))
      (terpri)
      ;; 2nd round:
      (if (<f i 10)
          (format t ";;;  |~D|-" i)
          (format t ";;;  |~D|" i))
      (princ (if (>= (car level-list) i) ">" "-"))
      (loop with node = head
            for j on level-list
            for n = 1 then (1+ n)
            until (or (eq node tail) (> n print-limit))
            do
        (if (>=f (car j) i)
            (progn
              (setq node (skip-list-element-next-n node i))
              (if (=f i 0)
		  (format t "|~A|-" (skip-list-element-key node))
		(format t "|~A|-" (skip-list-element-entry node))))
          (format t "----"))
        (princ (if (>= (or (cadr j) most-positive-fixnum) i) ">" "-")))
      (if (>f n-element print-limit)
          (format t "...~%")
        (format t "null~%"))
      ;; 3rd round
      (if (<f i 10)
          (format t ";;;  +-+  ")
          (format t ";;;  +--+ "))
      (loop with node = head
            for j on level-list
            for n = 1 then (1+ n)
            until (or (eq node tail) (> n print-limit))
            do
        (if (>=f (car j) i)
            (progn
              (setq node (skip-list-element-next-n node i))
              (format t "+-+  "))
          (format t "     ")))
      (terpri)
      ;; 4th round (i /= 0)
      (when (=f i 0) (return))
      (format t ";;;   |   ")
      (loop with node = head
            for j on level-list
            for n = 1 then (1+ n)
            until (or (eq node tail) (>f n print-limit))
            do
        (if (>=f (car j) i)
            (progn
              (setq node (skip-list-element-next-n node i))
              (format t " |   "))
          (format t "     ")))
      (terpri))
    (terpri)
    element-list))

#+development
(defun describe-large-skip-list (skip-list)
  (let ((head (skip-list-head skip-list))
        (tail (skip-list-tail skip-list))
        (level-list nil)
        (max-level 0)
        (element-list nil)
        (n-element 0))
    ;; get level 0 element first
    (loop for node = (skip-list-element-next-0 head)
                then (skip-list-element-next-0 node)
          until (eq node tail)
          maximize (skip-list-element-top-level node) into m
          finally (setq max-level m)
          do
      (push (skip-list-element-top-level node) level-list)
      (push (skip-list-element-key node) element-list)
      (incf n-element))
    (setq level-list (nreverse level-list))
    (setq element-list (nreverse element-list))
    ;; print the table
    (unless level-list
      (format t "Skip-list is empty.~%")
      (return-from describe-large-skip-list))
    (loop for i from max-level downto 0 do
      (format t "Level ~2D: " i)
      (loop with node = head
            for j in level-list
            for n = 1 then (1+ n)
            until (eq node tail)
            do
        (if (>= j i)
            (format t "#")
            (format t " ")))
      (terpri))
    (terpri)
    element-list))

;; A compatibility layer for exist binary trees.
(defmacro def-skip-list-or-binary-tree
    (name &key (constructor nil)
               (reclaimer nil)
               (clearer nil)
               (accessor nil)
               (accessor-given-hash nil)
               (key-deleter nil)
               (key-deleter-given-hash nil)
               (set-if-no-entry-given-hash nil)
               (hash-function 'sxhashw)
               (key-comparitor 'eq)
               (key-reclaimer nil)
               (entry-reclaimer nil)
               (flattener nil)
               (max-level 31)
               (use-binary-tree nil))
  (declare (ignorable max-level use-binary-tree))
  (let ((use-skip-list
         (current-system-case
           (ab #+skip-list (not use-binary-tree)
               #-skip-list nil)
           (t nil))))
    `(,(if use-skip-list
           'def-skip-list
           'def-binary-tree)
      ,name
      :constructor ,constructor
      :reclaimer ,reclaimer
      :clearer ,clearer
      :accessor ,accessor
      :accessor-given-hash ,accessor-given-hash
      :key-deleter ,key-deleter
      :key-deleter-given-hash ,key-deleter-given-hash
      :set-if-no-entry-given-hash ,set-if-no-entry-given-hash
      :hash-function ,hash-function
      :key-comparitor ,key-comparitor
      :key-reclaimer ,key-reclaimer
      :entry-reclaimer ,entry-reclaimer
      :flattener ,flattener
      ,@(when use-skip-list
          `(:max-level ,max-level)))))
