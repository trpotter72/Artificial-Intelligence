;;****************************************************************************
;; MATCHER.LISP
;;  for ICARUS 2017
;;  written by Dongkyu Choi
;;             Trenton R. Potter
;;****************************************************************************

; ORIGINAL FUNCTION HIERARCHY FOR THE STANDARD MATCHER:
; (* denotes a lowest-level function.)
; (All functions are in MATCHER.LISP except otherwise noted.)
;
; INFER
;   |- INFER
;   |- GET-MATCHES
;        |- MATCH-PCONDS
;             |- MATCH-PCOND
;                  |- PMATCHES* (STANFORDCOMPATIBLE.LISP)
;                  |- MATCH-PCONDS
;        |- MATCH-BCONDS
;             |- MATCH-BCONDS-AUX
;                  |- MATCH-BCOND
;                       |- MAKE-CINSTANCE
;                       |- BMATCHES*
;                       |- MATCH-BCONDS-AUX
;             |- NONE-MATCH
;                  |- MATCH-NCOND
;                       |- NMATCHES*
;                  |- NONE-MATCH
;        |- MATCH-TESTS
;             |- QSUBST-BINDINGS
;                  |- QSUBST-BINDINGS*
;             |- MATCH-TESTS
;        |- NONE-MATCH
;             |- MATCH-NCOND
;                  |- NMATCHES*
;             |- NONE-MATCH
;        |- MAKE-CINSTANCE
;        |- GET-POS-SUB-HEADS
;             |- SUBST-BINDINGS
;                  |- SUBST-BINDINGS*
;        |- GET-NEG-SUB-HEADS
;             |- SUBST-BINDINGS
;                  |- SUBST-BINDINGS*
;        |- GET-PERCEPTS
;             |- COLLECT-TEST-VARS
;                  |- COLLECT-TEST-VARS*
;             |- GET-VARS*
;             |- REMOVE-DUPLICATES
;        |- GET-ALL-PERCEPTS
;             |- LOOKUP-BELIEF*
;             |- REMOVE-DUPLICATES
;             |- GET-ALL-PERCEPTS
;        |- MATCH-PARTIAL-TESTS
;             |- MATCH-TESTS
;                  |- QSUBST-BINDINGS
;                       |- QSUBST-BINDINGS*
;                  |- MATCH-TESTS
;             |- GET-DEGREE-OF-MATCH
;                  |- GAUSSIAN*
;        |- SUBST-BINDINGS
;             |- SUBST-BINDINGS*
;        |- INSTANTIATE-ARGS
;             |- INSTANTIATE-ARGS*

(defvar cstm* nil)
(defvar inference* nil)
(defvar cycle* 1)

(defun variablep (sym-name)
 (cond ((atom sym-name)
	(cond ((numberp sym-name)
	       nil)
	      (t
	       (eq (elt (symbol-name sym-name) 0) #\?))))))

(defun start-time (belief)
  (car (cinstance-time-stamps belief)))

(defun end-time (belief)
  (cdr (cinstance-time-stamps belief)))

(defun same-meaning (b1 b2)
  ;; beliefs encode the same meaning if their heads are fully-instantiated and match
  (let ((head1 (cinstance-head b1))
	(head2 (cinstance-head b2)))
    (and (fully-instantiated head1)
	 (fully-instantiated head2)
	 (equal head1 head2))))

(defun fully-instantiated (clause)
  ;; true if the clause contains no variable
  (loop for sym in clause
       never (variable-p sym)))

; Need improved version of INFER that makes multiple passes.
(defun infer (concepts beliefs &key avoidlist)
  (let (new-inference)
    (loop for concept in concepts
	  do (prog ((inferences (get-matches concept beliefs)))
		   ;;(terpri)(princ "Inferred: ")(princ inferences)))
		   (loop for inference in inferences
			 do (prog ((analog (member inference beliefs :test 'same-cinstance))
				   (forbidden (member inference avoidlist :test #'same-meaning)))
				  (cond ((and (null analog) (null forbidden))
					 (setq new-inference t)
					 (push inference beliefs))
					(t nil))))))
    (cond ((null new-inference) beliefs)
	  (t
	   (infer concepts beliefs :avoidlist avoidlist)))))

; MATCH-BCONDS finds all matches between the Boolean conditions in CLIST
; and the Boolean elements in ELIST, with EMATCHED and BINDINGS holding
; the elements and bindings collected so far. It returns a list of lists,
; with the car of each component being a list of variable bindings and
; the cdr being the matched elements.
;  clist:     conditions (concepts) to match
;  elist:     concept instances that are true in the current state
;  ematched:  conditions that are matched so far
;  bindings:  bindings used in the conditions matched so far
;  novel:     switch for novel instance check
;  identity:  making a binding that is the identity relation
(defun match-bconds (clist elist ematched bindings
		     &optional (novel nil) (identity nil) (ignore-not-eq nil))
  (cond ((null clist) (list (cons bindings ematched)))
; ((testp (caar clist))
; (match-test (car clist) (cdr clist) elist ematched bindings))
	((not (null elist))
	 (let (positives negatives results)
	   (mapcar #'(lambda (condition)
		       (cond ((equal (car condition) 'NOT)
			      (push (cadr condition) negatives))
			     (t
			      (push condition positives))))
		   clist)
	   (when positives
	     (setq results
		   (match-bconds-aux positives elist ematched bindings novel
				     identity ignore-not-eq)))
	   (when negatives
	     (setq results
		   (remove-if-not #'(lambda (result)
				      (none-match negatives elist (car result)))
				  results)))
	   results))))

(defun match-bconds-aux (clist elist ematched bindings novel
			 &optional (identity nil) (ignore-not-eq nil))
  (cond ((null clist) (list (cons bindings ematched)))
	((not (null elist))
	 (match-bcond (car clist) (cdr clist) elist ematched bindings
		      novel identity ignore-not-eq))))

; MATCH-BCOND is called by MATCH-BCONDS (which it calls recursively) to
; handle matching for a single condition.
;  condition: a condition (a concept) to match
;  clist:     rest of conditions (concepts) to match
;  elist:     concept instances that are true in the current state
;  ematched:  conditions that are matched so far
;  bindings:  bindings used in the conditions matched so far
;  novel:     switch for novel instance check
(defun match-bcond (condition clist elist ematched bindings
			      &optional (novel nil) (identity nil) (ignore-not-eq nil))
  (let ((ecopy elist)
	(results nil))
    (do ((enext (car elist) (car elist)))
	((null elist) results)
      (cond ((cinstance-p enext))
	    (t
	     (warn "WARNING: In MATCH-BCOND, ELIST includes a non-CINSTANCE!")
	     (setq enext (make-cinstance :head enext))))
      (let ((bnext (bmatches condition enext bindings novel identity ignore-not-eq)))
	(cond ((not (null (car bnext)))
	       (setq results
		     (append (match-bconds-aux clist ecopy
					       (cons enext ematched) (cdr bnext)
					       novel identity ignore-not-eq)
			     results)))))
      (pop elist))))

;bmatches is compatible with McGyver changes if clist is in the predicate
;format, not in the head structure.

; TLP_EXP
; BMATCHES checks if clist matches elist and returns (FLAG . BINDINGS).
;  clist:    a concept head to match
;  elist:    a concept instance that is true in the current state
;  bindings: bindings collected so far
;  novel:    novel instance checker
(defun bmatches (clist elist bindings
		 &optional (novel nil) (identity nil) (ignore-not-eq nil))
  (let ((timecheck (time-stamped clist))
	(orig-bindings (copy-list bindings))
	head start end)
    (cond
      ; if clist is not time-stamped
      ((null timecheck)
       (setq head clist)
       (setq end 'NOW)) ; needs a fix pending Gary's response -DKC
      ; if clist is time-stamped
      (t
       (setq head (car clist))
       (setq start (second clist))
       (setq end (third clist))))
    ;If clist is a head structure call the helper
    (if (head-p head)
	(bmatches-helper head elist bindings start end novel identity ignore-not-eq)
    ;If not, proceed with the old code.
      (cond
       ; if concept names don't match
       ((not (equal (car head) (cinstance-name elist)))
	(cons nil bindings))
       ; if concept names match
       (t
	(let* ((degmatch (cinstance-degmatch elist))
	       (flag (if (and (numberp degmatch)
			      (< degmatch 1.0))
			 degmatch t))
	       (cargs (cdr head))
	       (ctimes (list start end))
	       (eargs
		(cdr (cinstance-head elist)))
		;;(cinstance-args-with-attributes elist))
	       (etimes (list (start-time elist) (end-time elist))))
	  (when dbg-retrieve*
	    (terpri)(princ "cargs: ")(princ cargs)
	    (terpri)(princ "eargs: ")(princ eargs)(terpri))

	  (do ((index 0 (1+ index)))
	      ((or (null flag)
		   (= index (length cargs)))
	       (if flag
		   (match-time-stamps ctimes etimes bindings
				      flag novel identity ignore-not-eq)
		 (cons flag orig-bindings)))
	    (let ((c (nth index cargs)))
	      ; if c is an attribute name that starts with ^
	      (cond ((attributep c)
		     (let (found)
		       (do ((i 0 (1+ i)))
			   ((or found
				(= i (length eargs)))
			    (if (null found)
				(setq flag nil)))
			 (cond ((equal (nth i eargs) c)
				(setq index (1+ index))
				(setq c (nth index cargs))
				(let ((result
				       (bmatches-aux c (nth (1+ i) eargs)
						     bindings flag
						     novel identity ignore-not-eq)))
				  (setq flag (car result))
				  (setq bindings (cdr result)))
				(setq found 't))))))
		    ; if c is not an attribute name
		    (t
		     (when dbg-retrieve*
		       (format t "c: ~A~%e: ~A~%" c (nth index eargs)))
		     (let ((result
			    (bmatches-aux c (nth index eargs)
					  bindings flag novel identity ignore-not-eq)))
		       (setq flag (car result))
		       (setq bindings (cdr result)))))))))))))

(defun match-time-stamps (ctimes etimes bindings flag novel identity ignore-not-eq)
  (let ((result (bmatches-aux (first ctimes) (first etimes) bindings
			      flag novel identity ignore-not-eq)))
    (bmatches-aux (second ctimes) (second etimes) (cdr result) (car result)
		  novel identity ignore-not-eq)))

(defun bmatches-aux (c e bindings flag novel identity)
  (cond
   ; if c is a space-filler (null)
   ((null c))
   ; if c is a constant
   ((not (variablep c))
    (cond ((and (not (equal c e))) (setq flag nil))
	  (t
	   (if novel
	       (push (cons c e) bindings)))))
   ; if c is a variable and it exists in bindings
   ((setq b (assoc c bindings))
    (cond ((not (equal (cdr b) e))
	   (setq flag nil))))
   ; When IDENTITY is nil, do not add the binding
   ; if c and e are the same variables.
   ; If they are all variables but different, the binding is
   ; added for unification later.
   ((and (variablep e)
	 (equal c e))
    (if identity (push (cons c e) bindings)))
   (t (push (cons c e) bindings)))
  (cons flag bindings))

#| Patch from DHM |#
(defun bmatches-aux (c e bindings flag novel identity
		     &optional ignore-not-eq)
  (when (or log-exp-equal*)
    (log-message (list "C: ~A~%E: ~A~%Bindings: ~A~%Bind Constants?: ~A~%" c e bindings ignore-not-eq))
    ;;(break)
    )
  (let (b)
    (cond
      ;; if c is a space-filler (null)
      ((null c))
      ;; if e is a list of predicates
      ((listp c)
       (when (or log-exp-equal*)
	 (log-message (list "C is a list!~%")))
       (let (unification)
	 ;; we set bind-constat-to-var to t in unify here
	 (setq unification (unify c e no-bindings t ignore-not-eq t))
	 (cond ((null unification)
		(when (or log-exp-equal*)
		  (log-message (list "Unification failed on ~A and ~A~%Bindings used: ~A.~%" c e 'no-bindings)))
		(setq flag nil))
	       (t
		(when (or log-exp-equal*)
		  (log-message (list "Unification SUCCESS on ~A and ~A~%Unified Bindings: ~A.~%Original Bindings: ~A~%" c e unification bindings)))
		(loop
		   named add-unified-bindings
		   for binding in unification
		   do
		     (cond ((and identity
				 (null (assoc (car binding) bindings))
				 (equal (car binding) (cdr binding)))
			    (push binding bindings))
			   ((and (not identity)
				 (null (assoc (car binding) bindings)))
			    (push binding bindings))

			   ((not (equal (cdr binding)
					(cdr (assoc (car binding) bindings))))
			    (when (or log-exp-equal*)
			      (log-message (list "Failure on ~A and ~A while adding unified bindings.~%" binding (assoc (car binding) bindings)))
			      (log-message (list "Identity: ~A~%" identity)))
			    (setq flag nil))))))))
      ;; if c is a constant
      ((not (variablep c))
       (when dbg-retrieve*
	 (format t "C (~A) is a constant!~%" c)
	 ;;(break)
	 )
       (let ((temp-binding1 (rassoc e bindings))
	     (temp-binding2 (assoc c bindings)))
	 (cond (ignore-not-eq
		(when dbg-retrieve*
		  (format t "ignoring not equal.~%"))
		;; When e is already bound, it better be bound to c
		(cond (temp-binding1
		       (when (not (equal (car temp-binding1) c))
			   (setq flag nil)))
		      ;; when c is already bound, it better be bound to e
		      (temp-binding2
		       (when (not (equal (cdr temp-binding2) e))
			 (setq flag nil)))
		      ((not temp-binding2)
		       (when novel
			 (if (or (listp e)
				 (listp c))
			     (push (cons c (list e)) bindings)
			     (push (cons c e) bindings))))))
	       ((not (equal c e))
		(when dbg-retrieve*
		  (format t "C (~A) != E (~A)...problemo :'(~%" c e)
		  ;;(break)
		  )
		(setq flag nil))
	       (t
		(when dbg-retrieve*
		  (format t "C = E. Novel is ~A~%" novel))
		(when novel
		  (if (or (listp e)
			  (listp c))
		      (push nil bindings)
		      (push (cons c e) bindings)))
		(when dbg-retrieve*
		  (format t "Returning.~%")
		  ;;(break)
		  )))))
      ;; if c is a variable and it exists in bindings
      ((setq b (assoc c bindings))
       (when dbg-retrieve*
	 (format t "C is a variable and exists in bingings :)~%")
	 ;;(break)
	 )
       (cond ((not (equal (cdr b) e))
	      (when dbg-retrieve*
		(format t "~A is bound to something other than ~A~%" (car b) e)
		;;(break)
		)
	      (setq flag nil))))
      ;; When IDENTITY is nil, do not add the binding
      ;; if c and e are the same variables.
      ;; If they are all variables but different, the binding is
      ;; added for unification later.
      ((and (variablep e)
	    (equal c e))
       (if identity (push (cons c e) bindings)))
      (t
       (when dbg-retrieve*
	 (format t "C (~A) is not in bindings, so adding (~A . ~A).~%" c c e))
       (if (or (listp c)
	       (listp e))
	   (push (cons c (list e)) bindings)
	   (push (cons c e) bindings))))
    (cons flag bindings)))


(defun bmatches-helper (head elist bindings start end novel identity &optional (ignore-not-eq nil))
  (let ((orig-bindings (copy-list bindings)))
    (cond
   ; if concept names don't match
     ((not (equal (head-name head) (cinstance-name elist)))
      (cons nil bindings))
   ; if concept names do match
     (t
      (let* ((degmatch (cinstance-degmatch elist))
             (flag (if (and (numberp degmatch)
                        (< degmatch 1.0))
                    degmatch t))
             (cargs (append (head-values head) (list start end)))
             (eargs (append (cinstance-args elist)
                     (list (start-time elist) (end-time elist)))))
       (do ((index 0 (1+ index)))
           ((or (null flag)
             (= index (length cargs)))
            (if flag
             (cons flag bindings)
             (cons flag orig-bindings)))
          (let ((c (nth index cargs)))
             ; if c is an attribute name that starts with ^
             (cond ((attributep c)
                    (let (found)
                        (do ((i 0 (1+ i)))
                         ((or found
                           (= i (length eargs)))
                          (if (null found)
                           (setq flag nil)))
                         (cond ((equal (nth i eargs) c)
                                (setq index (1+ index))
                                (setq c (nth index cargs))
                                (let ((result
                                           (bmatches-aux c (nth (1+ i) eargs)
                                                 bindings flag
                                                 novel identity ignore-not-eq)))
                                     (setq flag (car result))
                                     (setq bindings (cdr result)))
                                (setq found 't))))))
                                    ; if c is not an attribute name
              (t
                 (let ((result
                        (bmatches-aux c (nth index eargs)
                             bindings flag novel identity ignore-not-eq)))
                     (setq flag (car result))
                     (setq bindings (cdr result))))))))))))

;TLP_EXP
; GET-MATCHES that uses CINSTANCE structures with DEGMATCH attributes
(defun get-matches (concept beliefs)
  (loop
   with head = (concept-head concept)
   and id = (concept-id concept)
   and elements = (concept-elements concept)
   and tests = (concept-tests concept)
   and binds = (concept-binds concept)
   and pivot = nil
   and threshold = nil
   and inferences = (if (equal inference* 'fast) (concept-instances concept))

   for (bindings matched) in (match-bconds elements beliefs nil nil)
   do
   ;;(terpri)(princ "bindings: ")(princ bindings)
   
   (prog ((belief-head (copy-list head)))
	 (cond
	  ;;If using the fast matcher
	  ((and (equal inference* 'fast)
		(member belief-head inferences
			:key #'cinstance-head :test #'equal))
	   t)
	  ((and (null pivot)
		(match-tests tests bindings))
	   
	   ;;(terpri)(princ "bindings before: ")(princ bindings)
	   
	   ;;If there are local variables defined in the concept
	   (when binds
	     ;;(terpri)(princ "bindings before: ")(princ bindings)
	     ;;Process :binds field to get new bindings
	     ;; for derived objects
	     ;;Assumes that the compiler puts each definition in a list
	     (dolist (onedef binds)
	       (let ((variable (car onedef))
		     (formula (cadr onedef)))
		 ;;TO DO: Currently not checking if the formula is
		 ;;       fully instantiated.
		 (push (cons variable (eval (subst-bindings bindings
							    formula)))
		       bindings))))
	   
	   ;;(terpri)(princ "bindings after: ")(princ bindings)
	   
	   (cond ((equal inference* 'fast)
		  (push (make-cinstance
			 :head belief-head
			 :id (gensym (concatenate 'string
						  (princ-to-string id)
						  "-"))
			 :bindings bindings
			 :derived-object (not (null binds))
			 :pos-dependencies
			 (get-pos-sub-heads concept bindings)
			 :neg-dependencies
			 (get-neg-sub-heads concept bindings))
			inferences)
		  (get-all-percepts (first inferences)))
		 (t
		  (push (make-cinstance
			 :head (subst-bindings bindings belief-head)
			 :id (gensym (concatenate 'string
						  (princ-to-string id)
						  "-"))
			 :bindings bindings
			 :derived-object (not (null binds)))
			;;:time-stamps (cons cycle* 'NOW))
			inferences))))
	  ;;McGyver changes does not work with pivots yet.
	  ((and pivot
		(cond ((null negatives) t)
		      (t (none-match negatives beliefs bindings))))
	   (let ((degmatch (match-partial-tests tests bindings pivot))
		 (ihead (subst-bindings bindings head))
		 (args (instantiate-args (cdr head) bindings)))
	     (unless (or (not (numberp degmatch))
			 (and (numberp (car threshold))
			      ;;for now assume degmatch is not a list
			      ;;and threshold is a list. This will change soon.
			      (< (abs degmatch) (car threshold))))
	       ;;(terpri)(princ "DEGMATCH: ")(princ degmatch)
	       ;;(princ "THRESHOLD: ")(princ (car threshold))
	       (push (make-cinstance
		      :head ihead
		      :id (gensym (concatenate 'string
					       (princ-to-string id)
					       "-"))
		      :degmatch degmatch
		      :bindings bindings)
		     inferences))))))

   ;;Finally statements run once the loop has completed
   finally
   ;;(terpri)(princ "inferences: ")(princ inferences)
   (if (equal inference* 'fast)
       (setf (concept-instances concept) inferences)
     ;loop does not automatically return inferences, so force it
     (return-from get-matches inferences))))

(defun match-tests (clist bindings)
  (cond ((null clist) t)
	((eval (qsubst-bindings bindings (car clist)))
	 (match-tests (cdr clist) bindings))))

; QSUBST-BINDINGS is just like SUBST-BINDINGS except that it embeds the
; substituted value in quotes for later evaluation.

(defun qsubst-bindings (bindings generic)
  (cond ((null bindings) generic)
	(t (qsubst-bindings (cdr bindings)
			    (subst (list 'quote (cdar bindings))
				   (caar bindings) generic)))))

; NONE-MATCH inputs a set of (negated) conditions, a set of elements
; from conceptual short-term memory, and a set of bindings. It returns
; NIL if any ONE of the conditions match successfully and T otherwise.
; See NMATCHES below for details about how it treats variables.

;(defun none-match (clist elist bindings)
;  (cond ((null clist) t)
;	((match-ncond (car clist) elist bindings) nil)
;	(t (none-match (cdr clist) elist bindings))))

; NONE-MATCH inputs a set of conditions, a set of elements
; from conceptual short-term memory, and a set of bindings. It returns
; NIL if any ONE of the conditions match successfully and T otherwise.
; See NMATCHES below for details about how it treats variables.

(defun none-match (clist elist bindings)
  (cond ((null clist) t)
	((match-bcond (car clist) nil elist nil bindings) nil)
	(t (none-match (cdr clist) elist bindings))))

;;Choi: Why can't we use MATCH-BCOND instead? Will use MATCH-BCOND for now.
; MATCH-NCOND inputs a condition, a a set of elements from conceptual
; short-term memory, and a set of bindings. It returns NIL if the
; condition matches any one of the elements given the bindings.
; See NMATCHES below for details about how it treats variables.

(defun match-ncond (condition elist bindings)
  (do ((enext (car elist) (car elist)))
      ((null elist) nil)
      (cond ((car (nmatches condition enext bindings))
	     (return t)))
      (pop elist)))

;;Choi: What is the difference between this and BMATCHES?
;; Why can't we use BMATCHES instead? Will use BMATCHES for now.
;TLP_EXP
; NMATCHES inputs a condition (CLIST), an element (ELIST), and a set of
; bindings. It returns a list of the form (T <bindings>) if the condition
; matches the element and a list of the form (NIL <bindings>) otherwise.
; NOTE: An unbound variable may NOT bind to any symbol that is already
; bound to some other variable.

(defun nmatches (clist elist bindings)
  (cond
   ;If concept names don't match, return NIL.
   ((not (equal (car clist) (cinstance-name elist)))
    (cons nil bindings))
   ;If concept names match, proceed with arguments.
   (t
    (let ((flag t)
          (cargs (cdr clist))
          (eargs (cinstance-args elist)))
      (do ((c (car cargs) (car cargs))
           (e (car eargs) (car eargs))
           (b nil nil))
       ((or (null flag) (null cargs))
        (cons flag bindings))
       (terpri)(princ "c: ")(princ c)
       (terpri)(princ "e: ")(princ e)
       (cond ((not (variablep c))
              (cond ((not (equal c e))(setq flag nil))))
        ((setq b (assoc c bindings))
         (cond ((not (equal (cdr b) e))
                (setq flag nil))))
        ((rassoc e bindings)
         (setq flag nil))
        (t (push (cons c e) bindings)))
       (pop cargs)
       (pop eargs))))))

; SUBST-BINDING inputs a list of variable bindings, like ((?X . A)(?Y . B)),
; and a generic skill or action, like (STACK ?X ?Y), and substitutes the 
; bindings for variables to produce a specific result, like (STACK A B).  

(defun subst-bindings (bindings generic)
  (cond ((null bindings) generic)
	(t (subst-bindings (cdr bindings)
			   (subst (cdar bindings) (caar bindings) generic)))))

(defun create-cinstances-for-percepts (percepts)
  (loop for percept in percepts
	collect (make-cinstance :head percept)))

;; Temporary definitions
(defvar dbg-retrieve* nil)
(defvar log-exp-equal* nil)
