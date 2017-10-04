; NEWMATCHER.LISP
;  written as part of MacGyver project
;          by Dongkyu Choi

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
(defun infer (concepts perceptions beliefs &key avoidlist)
 (let ((new-inference nil)
       (ccopy concepts))
   (do ((concept (car concepts) (car concepts)))
       ((null concepts)
        (cond ((null new-inference) beliefs)
              (t
;	       (terpri)(princ "Inferred so far: ")
;	       (princ (mapcar #'(lambda (oneinst)
;				  (subst-bindings
;				   (head-bindings (cinstance-head oneinst))
;				   (head-listform
;				    (cinstance-head oneinst)))) beliefs))
	       (infer ccopy perceptions beliefs :avoidlist avoidlist))))
;     (terpri)(princ "Inferring concept: ")
;     (princ (head-name (concept-head concept)))(princ " ")
;     (princ (concept-id concept))
;     (cond ((equal (concept-id concept) (concept-id (car (last cltm*))))
;	    (terpri)(princ "Infering with: ")(princ perceptions)
;	    (terpri)(princ "Infering with: ")(princ beliefs)))
     (let ((inferences (get-matches concept perceptions beliefs)))
;       (cond ((equal (concept-id concept) (concept-id (car (last cltm*))))
;	      (terpri)(princ "Inferred: ")(princ inferences)))
         (do ((inference (car inferences) (car inferences)))
             ((null inferences) nil)
;TLP_EXP
             (let ((analog (member inference beliefs :test 'same-cinstance))
		   (forbidden (member inference avoidlist :test #'same-meaning)))

               (cond ((and (null analog) (null forbidden))
		      ;; inference hasn't produced an analog for the belief, and it isn't on the avoid list
                      (setq new-inference t)
                      (push inference beliefs)
		      (when (cinstance-derived-object inference)
			;Add the derived object to the perceptual buffer
			(let ((head (cinstance-head inference)))
			  (push
			   (subst-bindings
			    (head-bindings head) (head-listform head))
			   pstm*))
			;make sure the change in pstm* is updated locally
			(setq perceptions pstm*)))
                     (t nil)))
             (pop inferences)))
       (pop concepts))))

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
			      (push condition negatives))
			     (t
			      (push condition positives))))
		   clist)
	   (setq results
		 (match-bconds-aux positives elist ematched bindings novel 
				   identity ignore-not-eq))
	   (setq results
		 (remove-if-not #'(lambda (result)
				    (none-match negatives elist (car result)))
				results))
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
	     (setq enext (make-cinstance :head
					 (make-head
					  :name (car enext)
					  :listform enext
					  :arguments (cdr enext)
					  :values (cdr enext))))))
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
	       (cargs (append (cdr head) (list start end)))
	       (eargs (append (cinstance-args-with-attributes elist)
			      (list (start-time elist) (end-time elist)))))
;	  (terpri)(princ "cargs: ")(princ cargs)
;	  (terpri)(princ "eargs: ")(princ eargs)

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
		       (setq bindings (cdr result)))))))))))))

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
		     &optional (ignore-not-eq nil))
  (let (b)
    (cond
      ;; if c is a space-filler (null)
      ((null c))
      ;; if c is a constant
      ((not (variablep c))
       (let ((temp-binding1 (rassoc e bindings))
	     (temp-binding2 (assoc c bindings)))
	 (cond (ignore-not-eq
		(cond (temp-binding1
		       (when (not (equal (car temp-binding1) c))
			 (setq flag nil)))
		      (temp-binding2
		       (when (not (equal (cdr temp-binding2) e))
			 (setq flag nil)))
		      ((not temp-binding2)
		       (if novel
			   (push (cons c e) bindings)))))
	       ((not (equal c e)) 
		(setq flag nil))
	       (t
		(if novel
		    (push (cons c e) bindings))))))
      ;; if c is a variable and it exists in bindings
      ((setq b (assoc c bindings))
       (cond ((not (equal (cdr b) e))
	      (setq flag nil))))
      ;; When IDENTITY is nil, do not add the binding
      ;; if c and e are the same variables.
      ;; If they are all variables but different, the binding is
      ;; added for unification later.
      ((and (variablep e)
	    (equal c e))
       (if identity (push (cons c e) bindings)))
      (t (push (cons c e) bindings)))
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
(defun get-matches (concept perceptions beliefs)
  (let* ((head (concept-head concept))
; removing the changes for revision 170 - see the svn log for revision 213
;	 (head-bindings (remove-if
;			 #'null
;			 (mapcar
;			  #'(lambda (belief)
;			      (let ((head-matches (bmatches head belief nil)))
;				(if (car head-matches) (cdr head-matches))))
;			  beliefs)))
	 (elements (concept-elements concept))
	 (positives (concept-positives concept))
	 (negatives (concept-negatives concept))
	 (tests (concept-tests concept))
	 (id (concept-id concept))
	 (attributes (concept-attributes concept))
;	 (pivot (concept-pivot concept))
;	 (threshold (concept-threshold concept))
	 pivot
	 threshold
	 (pmatches
;	  (if head-bindings
;	      (mapcan #'(lambda (head-binding)
;			  (match-pconds percepts perceptions
;					nil head-binding))
;		      head-bindings)
;	      (match-pconds percepts perceptions nil nil)))
	  (match-pconds elements perceptions nil nil))
	 (inferences (if (equal inference* 'fast)
			 (concept-instances concept))))
    ;(show "PMATCHES: " pmatches debug*)
    (do ((bmatches (match-bconds positives beliefs nil (caar pmatches))
		   (match-bconds positives beliefs nil (caar pmatches))))
	((null pmatches)
	 (if (equal inference* 'fast)
	     (setf (concept-instances concept) inferences)
	     inferences))
      (do ((bindings (caar bmatches) (caar bmatches)))
          ((null bmatches) nil)
        (let ((belief-head (copy-head head)))
          (cond
	   ;McGyver changes does not work with the fast matcher yet.
	    ((and (equal inference* 'fast)
		  (member belief-head inferences
			  :key #'cinstance-head :test #'equal))
	     t)
	    ((and (null pivot)
		  (match-tests tests bindings)
		  (cond ((null negatives) t)
			(t (none-match negatives beliefs bindings))))
	     (setf (head-id belief-head)
		   (gensym (concatenate 'string
					(princ-to-string id)
					"-")))
;	     (terpri)(princ "bindings before: ")(princ bindings)
	     (when attributes
	       ;(terpri)(princ "bindings before: ")(princ bindings)
	       ;Process :attributes field to get new bindings
	       ; for derived objects
	       (dolist (oneattr attributes)
		 (let ((variable (car oneattr))
		       (verb (cadr oneattr))
		       (formula (caddr oneattr)))
		   (when (equal verb 'is)
		     (push (cons variable (eval (subst-bindings bindings
								formula)))
			   bindings)))))
;when 'is' statements are not encapsulated with parentheses
;	       (do ((i 0 (+ i 3)))
;		   ((> i (length attributes)))
;		 (let ((variable (nth i attributes))
;		       (verb (nth (1+ i) attributes))
;		       (formula (nth (+ i 2) attributes)))
;		   (when (equal verb 'is)
;		     (push (cons variable (eval (subst-bindings bindings
;								formula)))
;			   bindings)))))
;	     (terpri)(princ "bindings after: ")(princ bindings)
	     (setf (head-bindings belief-head)
		   (remove-if-not #'(lambda (binding)
				      (member (car binding)
					      (head-values belief-head)
					      :test 'equal))
				  bindings))
	     (cond ((equal inference* 'fast)
		    (push (make-cinstance
			   :head belief-head
			   :id id
			   :bindings bindings
			   :derived-object (not (null attributes))
			   :pos-dependencies
			   (get-pos-sub-heads concept bindings)
			   :neg-dependencies
			   (get-neg-sub-heads concept bindings)
			   :percepts (get-percepts concept bindings))
			  inferences)
		    (get-all-percepts (first inferences)))
		   (t
		    (push (make-cinstance
			   :head belief-head
			   :id id
			   :bindings bindings
			   :derived-object (not (null attributes)))
;			   :time-stamps (cons cycle* 'NOW))
			  inferences))))
	    ;McGyver changes does not work with pivots yet.
	    ((and pivot
		  (cond ((null negatives) t)
			(t (none-match negatives beliefs bindings))))
	     (let ((degmatch (match-partial-tests tests bindings pivot))
		   (ihead (subst-bindings bindings head))
		   (args (instantiate-args (cdr head) bindings)))
	       (unless (or (not (numberp degmatch))
			   (and (numberp (car threshold))
			   ; for now assume degmatch is not a list
			   ; and threshold is a list. This will change soon.
				(< (abs degmatch) (car threshold))))
;		       (terpri)(princ "DEGMATCH: ")(princ degmatch)
;		       (princ "THRESHOLD: ")(princ (car threshold))
		 (push (make-cinstance
			:head ihead
			:id (gensym (concatenate 'string
						 (princ-to-string id)
						 "-"))
			:degmatch degmatch
			:bindings bindings)
		       inferences))))))
        (pop bmatches))
      (pop pmatches))))

; MATCH-PCONDS finds all matches between the perceptual conditions in CLIST
; and the Boolean perceptual in ELIST, with EMATCHED and BINDINGS holding 
; the elements and bindings collected so far. It returns a list of lists,
; with the car of each component being a list of variable bindings and 
; the cdr being the matched elements.
;
; Now 'clist' can have (<var> is <obj> ...) format.
(defun match-pconds (clist elist ematched bindings)
  (cond ((null clist) (list (cons bindings ematched)))
        ((not (null elist))
	 ;Dongkyu - probably not needed (the match-pcond call makes no sense)
	 (if (equal (second clist) 'is)
	     (match-pcond (subseq clist 0 3) (subseq clist 3) elist
			  ematched bindings)
	   ;Dongkyu - Just need this
	   (match-pcond (car clist) (cdr clist) elist ematched bindings)))))

; Now 'condition' can have (<var> is <obj>) format.
;     'elist' can have head structures (derived objects) in it.
(defun match-pcond (condition clist elist ematched bindings)
 (let ((ecopy elist)
       (results nil))
   (do ((enext (car elist) (car elist)))
       ((null elist) results)
     ;Does this 'member' function also work for head structures?
       (cond ((not (member enext ematched :test 'equal))
              (let ((pnext (pmatches condition enext bindings)))
                (cond ((not (null (car pnext)))
                       (setq results
                             (append (match-pconds clist ecopy
                                           (cons enext ematched) (cdr pnext))
                                     results)))))))
       (pop elist))))

;; OVERWRITES THE SAME NAMED FUNCTION IN MATCHER.LISP.
;; GAK - checks for constants named in the :percepts field
; PMATCHES inputs a perceptual pattern, a specific perceptual object, and
; a set of bindings (cast as a list of dotted pairs). It returns a list of
; the form (T ((?X . A)(?Y . B))) if the pattern matches and is consistent 
; with the initial bindings and returns a list of the form (NIL ((?X . A)))
; if the match fails or the bindings are inconsistent. 

; Now 'pattern' can have (<var> is <obj>) format.
;     'element' can be a head structure (for derived objects).
(defun pmatches (pattern element bindings)
  (let (ptype etype pname eid)
    (cond ((and (equal (second pattern) 'is)
		(listp (third pattern)))
	   (setq ptype (car (third pattern)))
	   (setq pname (first pattern))
	   (setq pattern (third pattern)))
	  (t
	   (setq ptype (car pattern))
	   (setq pname (cadr pattern))))
    ;if element is a derived object in the form of a head structure
    (cond ((head-p element)
	   (setq eid (head-id element))
	   (setq etype (head-name element))
	   (setq element (subst-bindings (head-bindings element)
					 (head-listform element))))
	  (t
	   (setq etype (car element))))
;    (terpri)(princ "ptype: ")(princ ptype)
;    (terpri)(princ "pname: ")(princ pname)
;    (terpri)(princ "pattern: ")(princ pattern)
;    (terpri)(princ "etype: ")(princ etype)
;    (terpri)(princ "eid: ")(princ eid)
;    (terpri)(princ "element: ")(princ element)
    ;if the names match
    (cond ((eq ptype etype)
	   ;remove names
	   (setq pattern (cdr pattern))
	   (setq element (cdr element))
	   (let ((flag t))
	     (do ((i 0 (1+ i)))
		 ((= i (length pattern)))
	       (let ((one-pattern (nth i pattern))
		     variable (match t) value existing)
		       ;if the pattern is an attribute (starts with ^)
		 (cond ((attributep one-pattern)
			(incf i)
			(setq variable (nth i pattern))
			(setq match
			      (member one-pattern element :test 'equal))
			(setq value (cadr match)))
		       ;if the pattern is not an attribute
		       (t
			(setq variable one-pattern)
			(setq value (nth i element))))
;		 (terpri)(princ "variable: ")(princ variable)
;		 (terpri)(princ "value: ")(princ value)
		       ;if the pattern is a variable
		 (cond ((variablep variable)
			      ;if the binding already exists
			(cond ((setq existing
				     (assoc variable bindings))
;			       (terpri)(princ "existing binding: ")
;			       (princ existing)
			       (if (not (equal (cdr existing) value))
				   (setq flag nil)))
			      ;if the binding does not exist
			      (t
			       ;push binding if a match found, or
			       ;if the pattern is not an attribute
			       (if (or (and (attributep one-pattern)
					    match)
				       (not (attributep one-pattern)))
				   (push (cons variable value)
					 bindings)))))
		       ;if the pattern is a constant
		       (t
			(cond ((not (equal variable value))
;			       (terpri)(princ "Not equal constant")
			       (setq flag nil)))))))
;	     (terpri)(princ "flag: ")(princ flag)
	     (let ((nbind (assoc pname bindings)))
	           ;if the pattern name already exists in the bindings
	       (if nbind
		       ;if the existing binding is not equal to eid
		       ;and eid is not null
		   (if (and eid (not (equal (cdr nbind) eid)))
		       (setq flag nil))
		 ;if the pattern name does not exist in the bindings
		     ;if the pattern name is a variable
		 (if (variablep pname)
		         ;push binding if eid is not null
		     (if eid
			 (push (cons pname eid) bindings))
		   ;if the pattern name is a constant
		       ;if the pattern name is not equal to eid
		   (if (not (equal pname eid))
		       (setq flag nil)))))
	     (if flag
		 (cons flag bindings)
	       (cons nil bindings))))
	  (t
	   (cons nil bindings)))))

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

(defun none-match (clist elist bindings)
  (cond ((null clist) t)
	((match-ncond (car clist) elist bindings) nil)
	(t (none-match (cdr clist) elist bindings))))

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

(defun print-cstm (&optional (cstm cstm*))
  (mapcar #'(lambda (inst)
	      (let ((head (cinstance-head inst)))
		(subst-bindings
		 (head-bindings head)
		 (head-listform head))))
	  cstm))
