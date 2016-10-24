(in-package :lockfree)

;;; portable CAS

(defmacro compare-and-swap (place compare new-value &environment env)
  (declare (ignorable env))
  (progn
    ;; LispWorks 6.1 Release Notes (section 13.2.8):
    ;;
    ;; More places for which low-level atomic operations are defined:
    ;;
    ;; (the type place)
    ;;   For a place which is itself supported
    ;; (symbol-value symbol)
    ;;   This was documented (but not actually implemented) in LispWorks 6.0.
    ;; symbol
    ;;   This was implemented (but not documented) in LispWorks 6.0.
    #+(or SBCL LispWorks)
    (let ((old-value (gensym)))
      (setq place (macroexpand place env))
      (when (and (consp place)
		 (eq (car place) 'the)) ; handle (the fixnum ...) forms
	(setq place (third place)))

      ;; SBCL's CAS doesn't support atom place (global variable), so we must use
      ;; SYMBOL-VALUE explicitly. And it returns the old value, not boolean.
      `(let ((,old-value ,compare))
         #+SBCL
         (eq ,old-value
	     (sb-ext:cas ,(if (atom place) `(symbol-value ',place) place)
			 ,old-value ,new-value))
         #+LispWorks
         (sys:compare-and-swap ,place ,old-value ,new-value)))
    #+Clozure
    (progn
      (setq place (macroexpand place env))
      (when (and (consp place)
		 (eq (car place) 'the)) ; handle (the fixnum ...) forms
	(setq place (third place)))

      ;; CCL's CAS (CONDITIONAL-STORE) doesn't support CAR and CDR places, but
      ;; there're two replacements (%RPLACA/D-CONDITIONAL) to use instead.
      (if (and (consp place)
               (member (car place) '(car cdr first rest)))
          (ecase (car place)
            ((car first)
             `(ccl::%rplaca-conditional ,(cadr place) ,compare ,new-value))
            ((cdr rest)
             `(ccl::%rplacd-conditional ,(cadr place) ,compare ,new-value)))
        `(ccl::conditional-store ,place ,compare ,new-value)))
    #-(or LispWorks SBCL Clozure)
    (error "TODO: CAS is not supported in this platform!")))

(defmacro atomic-incff-decff (place delta)
  (let ((old (gensym))
	(new (gensym)))
    `(loop
       (let* ((,old ,place)
	      (,new (the fixnum (+ ,old ,delta))))
	 (declare (type fixnum ,old ,new))
	 (when (compare-and-swap ,place ,old ,new)
	   (return ,new))))))

(defmacro atomic-incff (place &optional (delta 1))
  `(atomic-incff-decff ,place ,delta))

(defmacro atomic-decff (place &optional (delta 1))
  `(atomic-incff-decff ,place (- ,delta)))

;;; Atomic reference

(defvar *all-atomic-references*	; ref->obj
  (make-hash-table :test 'eql))

(defvar *all-atomic-objects*	; obj->ref
  (make-hash-table :test 'eq))

(defvar *atomic-reference-counter*
  (cons #b111100000000000000000000000000000000000000000000 nil)) ; 48 bits, large enough

(defun get-pseudo-pointer () ; the so-called indirect reference
  (atomic-incff (car *atomic-reference-counter*) 8))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defconstant +atomic-stamp+ #x163)) ; #b000101100011

#|
Most-positive-fixnum (SBCL x64):
4611686018427387903 (#b0011111111111111111111111111111111111111111111111111111111111111)
Most-positive-fixnum (LispWorks & Clozure CL x64)
1152921504606846975 (#b0000111111111111111111111111111111111111111111111111111111111111)
Valid x64 pointer   (#b0000000000000000111111111111111111111111111111111111111111111111)
Valid Stamp         (#b0000111111111111000000000000000000000000000000000000000000000000)
Atomic Stamp        (#b0000000101100011000000000000000000000000000000000000000000000000)
|#

(defmacro make-atomic-reference (object &optional stamp)
  (let ((o (make-symbol "OBJECT"))
        (v (make-symbol "VALUE")))
    `(let* ((,o ,object)
            (,v (if ,o (gethash ,o *all-atomic-objects*) 0)))
       (unless ,v
         (setq ,v (get-pseudo-pointer))
         (setf (gethash ,o *all-atomic-objects*) ,v)
         (setf (gethash ,v *all-atomic-references*) ,o))
       (logiorf ,v (ashf ,(if (constantp stamp)
                              (if (eval stamp) #.+atomic-stamp+ 0)
                              `(if ,stamp #.+atomic-stamp+ 0))
                         48)))))

(defmacro atomic-reference-object (reference)
  (let ((v (make-symbol "VALUE"))
        (r (make-symbol "ATOMIC-REF")))
    `(let* ((,r ,reference)
            (,v (ldb (byte 48 0) ,r)))
       (if (=f ,v 0)
           nil
           (gethash ,v *all-atomic-references*)))))

(defmacro atomic-reference-equal (r1 r2)
  `(=f ,r1 ,r2))

(defmacro atomic-reference-neq (r1 r2)
  `(not (atomic-reference-equal ,r1 ,r2)))

(defmacro decrement-and-test-and-set (place)
  (let ((old (gensym))
	(new (gensym)))
    `(loop as ,old = ,place
	   as ,new = (-f ,old 2)
	   do
       (when (=f 0 ,new)
	 (setq ,new 1))
	   until (compare-and-swap ,place ,old ,new)
	   finally
	     (return (logand (-f ,old ,new) 1)))))

(defmacro clear-lowest-bit (place)
  (let ((old (gensym))
	(new (gensym)))
    `(loop as ,old = ,place
	   as ,new = (-f ,old 1)
	   until (compare-and-swap ,place ,old ,new))))
