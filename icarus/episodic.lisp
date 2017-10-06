(load "ep-log")

#| Debug flag for DHM's code |#
(defvar dhm-debug* nil)
(defvar dbg-variableize* nil)
(defvar dbg-insert* nil)
(defvar dbg-generalize* nil)
(defvar dbg-explain* nil)

#| Reference circular structures rather than print them all |#
(setf *print-circle* t)

#| Episodic Long Term Memory |#
(defvar eltm* '(:episodes '() :cache '()))

#| List to hold surprise frequencies |#
(defvar listforms* '())

#| Number for the number of numeric attributes we have generalized |#
(defvar numeric-atts* 0)

; Number of repetitions required before episodic learning happens
(defparameter learn-from-episodes-after-x-times* 3)

(defvar episodic-learning-threshold* 50)

#| Episodic memory episode. |#

; sigificant-relation = "surprising" belief in environment. Also can give context
; causal-event = event that caused surprising belief.
; sub-episodes = list of episodes that this one is derived from 
; event-sequences = state-action sequence that relates to this episode.
; id = gensym for episode id 
(defstruct episode
  significant-relation
  causal-event
  sub-episodes
  count)

#| Structure dictates 3 different types of significance |#

; threshold = The significant event happens relatively few times
; absence = This is a belief I expected to see, but isn't actually there
; repetition = This is a behavioral/relational pattern that is significant
(defstruct significance
  threshold
  absence
  repetition)

#| Episodic cache |#

; states = state sequence
; actions = action sequence
; episode = list of episode names in episodic memory
; bindings = bindings for that episode  
(defstruct cache
  states
  actions
  episodes
  bindings)

#| Node for the frequency tracker |#

;; name = name of the node. Can be listform, head, instance
;; parent = pointer to the parent of this node.
;; children = a list of more specified versions of this node
;; count = number of times this has occured
(defstruct epi-node
  name
  parent
  children
  (count 0))

#| Search a graph |#

; eps = list of sibling episodes
; ep = episode to insert
; qs = attributes we are checking consistency for
(defun insert-episode (eps ep qs)
  (when (or log-insert*
	    log-generalize*)
    (log-message (list "******************************~%"))
    (log-message (list "******Inserting Episode*******~%"))
    (log-message (list "******************************~%~%")))
  (let ((queue '())
	(temp (cdar eps))
	(match '())
	(p '()))
    (loop
       named sort
       while (not (null temp)) do
       ;; visit epi-node
	 (when (or log-insert*)
	   (log-message (list "Performing consistency check.~%")))
	 #|(when dbg-insert*
	   (trace consistent?))|#
	 (setq match (consistent? temp (cdr ep) qs 0))
	 (when (or log-insert*)
	   (log-message (list "Consistency check complete.~%~%")))
	 #|(when dbg-insert*
	 (untrace consistent?))|#
	 (cond ((= 1 match)
		(incf (episode-count temp))
		(return-from sort match))
	       ((or (not (= 0 match))
		    (equalp (make-significance) (episode-significant-relation temp)))
		(incf (episode-count temp))
		(when (and (not (equalp (make-significance)
					(episode-significant-relation temp)))
			   (>= (episode-count temp) 1))
		  #|(epi-learn (episode-significant-relation temp) 
		  (episode-causal-event temp)
		  'significance-threshold)|#)
		(setq queue '())
		(mapcar #'(lambda (sub)
			    (setq queue (reverse (cons sub (reverse queue)))))
			(episode-sub-episodes temp))
		;; (format t "Variables:~%~S~%" variables)
		#|(when (and (null (episode-sub-episodes temp))
		(is-general? temp))
		(setf (episode-sub-episodes temp) 
		(cons ep (episode-sub-episodes temp)))
		(sibling-generalize temp ep))|#
	   (setq p temp)))
	 (setq temp (cdar queue))
	 (setq queue (cdr queue)))
    (cond ((and (null temp)
	       (not (= 1 match)))
	   (when (or log-insert*)
	     (log-message (list "Match not exact. Inserting Episode.~%~%")))
	   (setf (episode-sub-episodes p) 
		 (cons ep (episode-sub-episodes p)))
	   (when dbg-generalize*
	     (format t "Before generalization:~%~%")
	     (eltm-to-pdf)
	     (break))
	   (when (or log-generalize*)
	     (log-message (list "Performing sibling generalization~%")))
	   (sibling-generalize p ep))
	  ((and (not (null temp))
		(= 1 match))
	   (when (or log-insert*)
	     (log-message (list "Incremented counter for fully instantiated episode.~%")))
	   (when (or dbg-insert*)
	     (format t "Incremented counter for fully instantiated episode.~%")))))
  (when (or log-generalize*)
	(log-message (list "Completed sibling generalization.~%~%")))
  (when (or dbg-insert*
	    dbg-generalize*)
    (format t "After generalization:~%")
    (eltm-to-pdf)
    (break))
  ;;(eltm-to-pdf)
  ;;(break)
  )

#| Make skill that is consistent with one experience |#

;; sigs = significant relation of the episode
;; causes = explanation
(defun epi-learn (sigs causes sig-type)
  ;; Perform a second level search
  ;; predata = [(the state action seq, action, sig-event)]
  (let ((person '())
	(predata (remove-duplicates 
		  (loop
		     for skillz in 
		       (loop
			  for state in (loop
					for explanation in (funcall sig-type causes)
					collect (first (last (mapcar #'first explanation))))
			  when (member 'my-person state :key 'cinstance-name)
			  if (eq 'none (cdr (assoc '?action (cinstance-bindings 
							     (car (member 'my-person state :key 'cinstance-name))))))
			  collect (list (list nil))
			  else
			  collect (list (list '*sit 
					      (cdr (assoc '?action 
							  (cinstance-bindings 
							   (car (member 'my-person state :key 'cinstance-name))))))))
		     nconcing (first-level-search (getf eltm* :episodes) 
						 'search-helper 
						 skillz
						 sig-type))
		  :test 'equal)))
    (format t "Predata:~%~S~%" predata)
    ;(break)
    (loop
       for predataset in predata
       do
	 (let* ((attribute-bels (remove-duplicates
				 (loop
				    for row in predataset
				    nconcing (copy-list (car row)))
				 :test 'equal))
		(blocks (lem2-wrapper attribute-bels predataset)))
	   (format t "d-star: ~S~%blocks:~%~S~%" (mapcar #'car (first blocks)) (second blocks))
	   ;(break)
	   (mapc #'(lambda (goal)
		      (let ((lhss (lem2 (second blocks) (car goal))))
			;; if an agent is in the env...learn the rule
			(format t "*********~%RULES~%*********~%~S" 
				(mapcar #'(lambda (lhs)
					    (learn-sclause (mapcar #'second lhs)
							   (instantiate-listform (cdr goal))
							   (second (car predataset))))
					lhss))
			;(break)
			(setq sltm* 
			      (append sltm* 
				      (mapcar #'(lambda (lhs)
						  (learn-sclause (butlast (mapcar #'second lhs))
								 (instantiate-listform (cdr goal))
								 (second (car predataset))))
					      lhss)))
				))
		 (first blocks))))))

(defun learn-sclause (elements effects actions)
  ;;(if (not (= -1 (nth 4 (car (member 'my-person elements :key 'first))))))
  (let ((ele-names (mapcar #'second elements)))
    (create-skill-clause 
     (list  (nconc (list (intern (symbol-name (gensym "SCLAUSE-")))) ele-names)
	    :elements (mapcar #'(lambda (ele-name ele)
				  (list ele-name 'IS ele))
			      ele-names elements)
	    :effects effects
	    :subskills actions))))

(defun get-subset-with-max (Tog)
  (loop
     for block in Tog
     with subset = '()
     with max-len = 0
     do (cond ((> (length (car block)) max-len)
	       (setq subset (list block))
	       (setq max-len (length (car block))))
	      ((= (length (car block)) max-len)
	       (push block subset)))
     finally (return subset)))

(defun get-smallest-cardinality (conditions applicable-tog)
  (loop
     for block in applicable-tog
     with subset = '()
     with smallest = most-positive-fixnum
     do 
       (cond ((< (length (car block)) smallest)
	       (setq subset (list (first (member (second block) conditions :key 'second :test 'equal))))
	       (setq smallest (length (car block))))
	      ((= (length (car block)) smallest)
	       (push (first (member (second block) conditions :key 'second :test 'equal)) subset)))
     finally (return subset)))

(defun get-ruleset-block (ruleset)
  (let ((mruleset (copy-tree ruleset)))
    (remove-duplicates 
     (loop
	for rule in mruleset
	nconcing (get-rule-block rule)))))

(defun get-rule-block (rule)
  (let ((mrule (copy-tree rule)))
    (remove-duplicates
     (loop 
	for condition in mrule
	nconcing (first condition)))))

(defun lem2 (s B)
  (let ((G (copy-list B))
	tau)
    (loop
       while (not (null G))
       do
	 (let ((rule '())
	       (Tog (mapcar #'(lambda (attval)
			      (cons (intersection (car attval) G) (list (second attval))))
			  s)))
	 (loop 
	    while (or (null rule) (not (subsetp (get-rule-block rule) G)))
	    do
	      ;;(format t "Rule: ~S~%Rule Block: ~S~%Goal Block: ~S~%" rule (get-rule-block rule) G)
	    ;; select a pair t member of Tog with the highest attribute priority. 
	    ;; Handle ties.
	      (let ((condition (get-subset-with-max Tog)))
		(cond ((> (length condition) 1)
		       (setq condition (get-smallest-cardinality condition
								 (intersection condition Tog 
									       :key 'second
									       :test 'equal))))
		      ((= (length condition) 1)
		       (setq condition (first condition)))
		      (t
		       (error "BAD RESULT FOR MAX SUBSET")))
		(format t "    Condition: ~S~%" condition)
		(setq rule (nconc condition rule))
		(format t "    Partial Rule: ~S~%" rule)
		(setq G (intersection (get-rule-block condition) G))
		(format t "    Goal Update: ~S~%" G)
		(setq Tog 
		      (mapcar #'(lambda (attval)
				  (cons (intersection (car attval) G) (list (second attval))))
			      s))
		(setq Tog (set-difference Tog rule :test 'equal))))
	 ;;Turn off dropping conditions for now because this mean
	 #|
	 (loop 
	    for condition in rule
	    do  
	      (when (and (> (length rule) 1)
			 (subsetp (get-rule-block (remove condition rule :test 'equal)) B))
		 (setq rule (remove condition rule :test 'equal)))) |#
	 (setq tau (cons rule tau))
	 (setq G (set-difference B (get-ruleset-block tau)))))
    (loop 
       for rule in tau
       do
	 (when (and (> (length tau) 1) 
		    (null (set-difference (get-ruleset-block (remove rule tau :test 'equal))
					  B))
		    (null (set-difference B 
					  (get-ruleset-block (remove rule tau :test 'equal)))))
	   (setq Tau (remove rule tau :test 'equal)))
       finally (return tau))))

#| Retrieve the decision partition |#

;; predata = list of datasets
(defun lem2-wrapper (bels predata)
  (let (blocks)
    (loop 
       for row upto (- (length predata) 1)
       with d-star = '()
       do
	 ;(format t "----------------------------------------~%")
	 (loop 
	    for condition in (first (nth row predata))
	    do 
	      ;(format t "Blocks: ~S~%Condition: ~S~%" blocks condition)
	      (if (not (member condition blocks :key 'second :test 'equal))
		  (setq blocks (cons (cons (list row) (list (copy-tree condition))) blocks))
		  (setf (car (first (member condition blocks 
					    :key 'second 
					    :test 'equal)))
			(union (car (first (member condition blocks 
						   :key 'second 
						   :test 'equal))) (list row))))
		  finally (return blocks))
	 ;(format t "----------------------------------------~%")
	 (if (null (rassoc (third (nth row predata)) d-star :test 'same-cinstance))
	     (setq d-star (cons (cons (list row) (third (nth row predata))) d-star))
	     (setf (car (rassoc (third (nth row predata)) d-star :test 'same-cinstance))
		   (union (car (rassoc (third (nth row predata)) d-star :test 'same-cinstance)) (list row))))
       finally (return (list d-star blocks)))))
#| Wrapper function for testing an episode from the eltm |#

;; skills1 = Instantiated skill listforms
;; eltm = episodic long term memory
;; sig-type = determines if this a significance of threshold, absence or repetition
(defun search-helper (skills1 sig-type eltm)
  (let (states skills effects)
    (loop
       for explanation in (funcall sig-type (episode-causal-event (cdr eltm)))
       for effect in (funcall sig-type (episode-significant-relation (cdr eltm)))
       when (skill-eq skills1 (loop 
				 for belief in (first (last (mapcar #'first explanation)))
				 when (eq 'my-person (cinstance-name belief))
				 if (eq 'none (cdr (assoc '?action (cinstance-bindings belief))))
				 collect (list 'nil)
				 else 
				 collect (list '*sit (cdr (assoc '?action (cinstance-bindings belief))))))
       collect (mapcar #'instantiate-listform (first (first explanation))) into states
       collect skills1 into skills
       collect effect into effects
       finally (return (mapcar #'list states skills effects)))))

(defun first-level-search (eltm function &rest fun-args)
  ;(format t "Action: ~S~%" (first fun-args))
  ;(break)
  (let* ((queue (episode-sub-episodes (cdr eltm)))
	(temp eltm)
	(match '()))
    (loop 
       while (not (null temp)) 
       do
       ;; test/visit epi-node
	 (setq match (funcall function 
			      (first fun-args)  
			      (second fun-args)
			      temp))
	 (setq temp (car queue))
	 (setq queue (cdr queue))
       when (not (null match))
       collect match))) ;; <-- used to be (first match)

#| Make sure instantiated skill heads are unifiable |#

;; skills1 = first skill trace
;; skills2 = second skill trace
(defun skill-eq (skills1 skills2)
  ;(break)
  (if (< (length skills2) (length skills1)) '()
      (notany #'null
	      (mapcar #'(lambda (skill1 skill2)
			  (equal (car skill1) (car skill2)))
		      skills1 (reverse (subseq (reverse skills2) 0 (length skills1)))))))

(defun instantiates-children? (general-ep children)
  (when (or log-generalize*)
    (log-message (list "******************************~%"))
    (log-message (list "****Instantiates Children?****~%"))
    (log-message (list "******************************~%~%")))
  
  (loop
     named instantiate-children
     for child in children
     when (= 0 (consistent? general-ep
			    child
			    '(episode-significant-relation
			      ;;episode-causal-event
			      )
			    0))
     do
       (when (or log-generalize*)
	 (log-message (list "Candidate Episode fails to instantiate child.~%")))
       (return-from instantiate-children nil)
     else
     do
       (when (or log-generalize*)
	 (log-message (list "Child instantiable by general candidate.~%")))
     finally
       (when (or log-generalize*)
	  (log-message (list "Candidate Episode instantiates children.~%")))
       (return-from instantiate-children t)))

#| Test to see if the general episode doesn't instantiate it's parent. |#

;; general-ep = generalized episode
;; p = parent episode of general-ep
;; children = potential children episodes of general-ep
(defun valid-generalization? (general-ep p children)
  (when (or log-generalize*)
    (log-message (list "******************************~%"))
    (log-message (list "***Validating Generalization**~%"))
    (log-message (list "******************************~%~%")))
  (when dbg-generalize*
    (format t "In (valid-generalization?)~%")
    (break))
  (cond ((and (equalp (episode-significant-relation p) (make-significance))
	      (equalp (episode-causal-event p) (make-significance))
	      (instantiates-children? (cdr general-ep) children))
	 (when (or log-generalize*)
	   (log-message (list "Parent episode is generic ep.~%"))
	   (log-message (list "General instantiates its children.~%"))
	   (log-message (list "Valid generalization.~%")))
	 t)
	(t (when dbg-generalize*
	     ;;(trace consistent?)
	     (format t "Testing if general episode instantiates parent.~%")
	     (break))
	   (when log-generalize*
	     (log-message
	      (list "Testing if general episode doesn't instantiate parent.~%"))
	     (log-message
	      (list "Testing if general episode instantiates children.~%")))
	   (and (= 0 (consistent? (cdr general-ep) p '(episode-significant-relation
						  ;;episode-causal-event
						       ) 0))
		(instantiates-children? (cdr general-ep) children)))))
#| Make an episodic generalization on the sibling level right after insertion.
   These episodes must have the same structure! So I just need to check if the bindings
   are consistent.|#

; p = parent of entry
; entry = newly inserted episode
(defun sibling-generalize (p entry)
  ;for each sibling, check to see what bindings are consistent to the entry

  (when (or log-generalize*)
    (log-message (list "******************************~%"))
    (log-message (list "******Sibling Generalize******~%"))
    (log-message (list "******************************~%~%")))

  (if (not (equal '() p))
  (let ((children (remove entry (episode-sub-episodes p) :test 'equal))
	(flag '())
	(general-ep '()))
    (when (or log-generalize*)
      (log-message (list "Parent has ~d children.~%" (length children))))
    (do ((child (cdar children) (cdar children)))
	((or (null children) general-ep)
	 flag)
      (when (or log-generalize*)
	(log-message (list "Attempting to create general episode.~%")))
      (setq general-ep (variableize child (cdr entry)))
      (when general-ep
	;; If general episode doesn't instantiate the parent, but insantiates its children,
	(when (or log-generalize*)
	  (log-message (list "Found candidate general episode.~%")))
	(when (and dhm-debug* (not dbg-variableize*)) 
	  (trace consistent? match-bconds match-bcond bmatches bmatches-aux))
	(cond ((valid-generalization? general-ep p (list (cdr entry) child))
	       (when (or dbg-generalize*)
		 (log-message (list "Created Valid Generalization.~%")))
	       (setq flag t)
	       (setf (episode-sub-episodes (cdr general-ep)) 
		     (list entry (car children)))
	       (setf (episode-sub-episodes p)
		     (remove-if #'(lambda (c)
				    (or (equal c entry)
					(equal c (car children))))
				(episode-sub-episodes p)))
	       (setf (episode-sub-episodes p)
		     (cons general-ep (episode-sub-episodes p)))
	       (setf (episode-count (cdr general-ep))
		     (reduce #'+ (mapcar #'(lambda (c)
					     (let ((child (cdr c)))
					       (episode-count child)))
					 (episode-sub-episodes (cdr general-ep)))))
	       (when (>= (episode-count (cdr general-ep)) learn-from-episodes-after-x-times*)
		 (epi-learn (episode-significant-relation (cdr general-ep)) 
			    (episode-causal-event (cdr general-ep))
			    'significance-threshold)))
	      (t
	       (when (or dbg-generalize*)
		 (log-message (list "Created invalid generalization.~%~%")))
	       (when (or dbg-generalize*)
		 (format t "Created invalid generalization.~%~%")
		 (break))
	       (setq general-ep '())))
	(when (and dhm-debug* (not dbg-variableize*)) 
	  (untrace consistent? match-bconds match-bcond bmatches bmatches-aux))
	(when (and dhm-debug* dbg-variableize*) 
	  (untrace match-bconds match-bcond bmatches bmatches-aux)))
      (pop children))
    #|(when dbg-generalize*
      (untrace consistent?))|#
    )))

(defun copy-sig-field (sig-field bindings)
  (mapcar #'(lambda (bel)
	      (let ((copy-bel (deep-copy-cinstance bel)))
		;; change the cinstance's bindings
		(setf (cinstance-bindings copy-bel) 
		      (subst-bindings bindings 
				      (cinstance-bindings copy-bel)))
		(setf (head-bindings (cinstance-head copy-bel))
		      (subst-bindings bindings
				      (head-bindings (cinstance-head copy-bel))))
		copy-bel))
	  sig-field))

(defun copy-causal-field (cause-field bindings)
  (mapcar #'(lambda (explanation)
	      (mapcar #'(lambda (state action)
			  (cons (copy-sig-field state bindings)
				(list (copy-list action))))
		      (mapcar #'first explanation)
		      (mapcar #'second explanation)))
	  cause-field))
  
(defun generate-generalized-bindings (temp actual bindings)
  #|(when (and dhm-debug* dbg-variableize*)
    (break)
  (traceo match-bconds match-bcond bmatches bmatches-aux))|#

  (when (or log-generalize*)
    (log-message (list "******************************~%"))
    (log-message (list "****Generalizing Bindings*****~%"))
    (log-message (list "******************************~%~%"))
    (log-message (list "Template Beliefs:~%~S~%"
		       (mapcar #'instantiate-listform temp)))
    (log-message (list "Actual Beliefs:~%~S~%"
		       (mapcar #'instantiate-listform actual)))
    (log-message (list "Current Bindings: ~S~%" bindings)))
  
  (let ((res (caar (match-bconds (mapcar #'instantiate-listform temp)
				 actual
				 nil
				 bindings
				 t ;; novel
				 t ;; identity
				 t ;; ignore-not-eq
				 ))))
    (when (or log-generalize*)
      ;(untrace match-bconds match-bcond bmatches bmatches-aux)
      (log-message (list "Returning Bindings: ~S~%" res))
      ;(break)
      )
    res))

#| variableize belief bindings in the state |#

;; template = reference episode
;; actual = newly entered episode
(defun variableize (template actual)
  (when (or log-generalize*)
    (log-message (list "******************************~%"))
    (log-message (list "*****Variablizing Episode*****~%"))
    (log-message (list "******************************~%~%")))
  (let ((temp-sig-thresh (significance-threshold 
			  (episode-significant-relation template)))
	(temp-sig-absence (significance-absence 
			   (episode-significant-relation template)))
	(temp-causal-thresh (significance-threshold 
			     (episode-causal-event template)))
	(temp-causal-absence (significance-absence 
			      (episode-causal-event template)))
	(actual-sig-thresh (significance-threshold 
			    (episode-significant-relation actual)))
	(actual-sig-absence (significance-absence 
			     (episode-significant-relation actual)))
	(actual-causal-thresh (significance-threshold 
			       (episode-causal-event actual)))
	(actual-causal-absence (significance-absence 
				(episode-causal-event actual)))
	(bindings '()))
    ;; for each state get the appropriate bindings
    (setq bindings (generate-generalized-bindings 
			       temp-sig-thresh 
			       actual-sig-thresh 
			       bindings))
    (setq bindings (generate-generalized-bindings 
		    temp-sig-absence 
		    actual-sig-absence 
		    bindings))

    (loop
       for explanation1 in temp-causal-thresh
       for explanation2 in actual-causal-thresh
       do (loop
	     for state1 in (mapcar #'first explanation1)
	     for state2 in (mapcar #'first explanation2)
	     do (setq bindings (generate-generalized-bindings
				state1
				state2
				bindings))))
    (when (or log-generalize*)
      (log-message (list "Bindings to variableize: ~A~%" bindings)))
    (when bindings
      ;; variableize the bindings
      (when (or log-generalize*)
	(log-message (list "Displaying bindings:~%")))
      (mapcar #'(lambda (binding)
		  (when (or log-generalize*)
		    (log-message (list "~S~%" binding)))
		  (if (or (listp (cdr binding))
			  (listp (car binding)))
		      nil
		      (when (not (eq (car binding) (cdr binding)))
			(setf (cdr binding)
			      (intern (concatenate 'string "?" (symbol-name (cdr binding))))))))
	      bindings)
      
      (when (and dhm-debug* dbg-variableize*)
	;;(trace subst-bindings subst)
	(format t "Generalized bindings: ~S~%" bindings)
	;(break)
	)
      (when (or log-generalize*)
	(log-message (list "Generalized bindings: ~S~%" bindings)))
      
      (let ((general-ep (make-episode :significant-relation
				      (make-significance 
				       :threshold
				       (copy-sig-field temp-sig-thresh bindings)
				       :absence
				       (copy-sig-field temp-sig-absence bindings))
				      :causal-event
				      (make-significance
				       :threshold
				       (copy-causal-field temp-causal-thresh bindings)
				       :absence
				       (copy-causal-field temp-causal-absence bindings))
				      :count 0)))
	(when (and dhm-debug* dbg-variableize*)
	  ;;(untrace subst-bindings subst)
	  (format t "General Episode:~%~S~%" general-ep)
	  ;(break)
	  )
	(cons (gensym "EPISODE-") general-ep)))))

#| variableize numeric bindings from the belief|#

;; bindings = bindings
(defun variableize-numeric-bindings (bindings)
  (mapcar #'(lambda(binding)
	      (if (numberp (cdr binding))
		  (let (num)
		    (incf numeric-atts*)
		    (setq num (write-to-string numeric-atts*))
		    (cons (car binding) (intern (concatenate 'string "?N" num)))) 
		  binding))
	  bindings))

(defun deep-copy-cinstance (cinstance)
  (when (not (null cinstance))
    (let ((new-cinstance (make-cinstance))
	  (new-head (make-head)))
      (setf (head-id new-head) (copy-symbol (head-id (cinstance-head cinstance))))
      (setf (head-name new-head) (head-name (cinstance-head cinstance)))
      (setf (head-listform new-head) (copy-list (head-listform (cinstance-head cinstance))))
      (setf (head-arguments new-head) (copy-list (head-arguments (cinstance-head cinstance))))
      (setf (head-values new-head) (copy-list (head-values (cinstance-head cinstance))))
      (setf (head-bindings new-head) (copy-tree (head-bindings (cinstance-head cinstance))))
      
      (setf (cinstance-head new-cinstance) new-head)
      (setf (cinstance-id new-cinstance) (copy-symbol (cinstance-id cinstance)))
      (setf (cinstance-bindings new-cinstance) (copy-tree (cinstance-bindings cinstance)))
      (setf (cinstance-subgoals new-cinstance) (copy-tree (cinstance-subgoals cinstance)))
      (setf (cinstance-pos-dependencies new-cinstance) 
	    (copy-tree (cinstance-pos-dependencies cinstance)))
      (setf (cinstance-neg-dependencies new-cinstance)
	    (copy-tree (cinstance-neg-dependencies cinstance)))
      (setf (cinstance-percepts new-cinstance)
	    (copy-tree (cinstance-percepts cinstance)))
      (setf (cinstance-total-percepts new-cinstance)
	    (copy-tree (cinstance-total-percepts cinstance)))
      (setf (cinstance-timestamp new-cinstance)
	    (copy-tree (cinstance-timestamp cinstance)))
      (if (cinstance-derived-object cinstance)
	  (setf (cinstance-derived-object new-cinstance) t)
	  (setf (cinstance-derived-object new-cinstance) '()))
      new-cinstance)))

(defun replace-bindings (belief bindings)
  ;; Remove numeric bindings from the general episode
  (setf (head-bindings (cinstance-head belief)) 
	(variableize-numeric-bindings (head-bindings (cinstance-head belief))))
  (setf (cinstance-bindings belief)
	(variableize-numeric-bindings (cinstance-bindings belief)))

  (let ((applicable-bindings
	 (remove 'nil 
		 (mapcar #'(lambda (binding)
			     (if (equal (symbol-name 
					 (head-id (cinstance-head belief)))
					(symbol-name (first binding)))
				 (second binding)))
			 bindings))))
    (mapcar #'(lambda (binding)
		(setf (head-bindings (cinstance-head belief))
		      (subst binding 
			     (assoc (car binding) (head-bindings (cinstance-head belief)))
			     (head-bindings (cinstance-head belief))))
		(setf (cinstance-bindings belief)
		      (subst binding 
			     (assoc (car binding) (cinstance-bindings belief))
			     (cinstance-bindings belief))))
	    applicable-bindings)))

#| See if two episodes unify in terms of the episodic cues |#

;; template = template episode to perform consistency
;; actual = episode I'm trying to insert to perform consistency on
;; qs = All episode attributes
;; code = result code of mequal test.
;;        0 - fail.
;;        1 - exact match.
;;        2 - generalized match.
(defun consistent? (template actual qs code)
  (when (or log-insert*
	    log-generalize*)
    (log-message (list "******************************~%"))
    (log-message (list "*****Checking Consistency*****~%"))
    (log-message (list "******************************~%~%"))
    ;;(log-message (list "Template Episode:~%~S~%" template))
    ;;(log-message (list "Actual Episode:~%~S~%" actual))
    (log-message (list "Episode Fields to check: ~S~%" qs))
    (log-message (list "Code: ~d~%~%" code)))

  (cond ((null qs)
	 (when (or log-insert*
		   log-generalize*)
	   (log-message (list "---------------------------------~%"))
	   (log-message
	    (list "Exhausted consistency checks.~%Returning ~d.~%"
		  code)))
	 (when (or dbg-generalize*
		   dbg-insert*)
	   (format t "Exhausted consistency checks.~%Returning ~d.~%"
		   code))
	 code)
	((null (mapcar #'instantiate-listform
		       (significance-threshold (funcall (first qs)
							template))))
	 (when (or log-insert*
		   log-generalize*)
	   (log-message (list "---------------------------------~%"))
	   (log-message (list "Template Belliefs are null. Failing.~%")))
	 (when (or dbg-generalize*
		   dbg-insert*)
	   (format t "Template Beliefs are null. Failing.~%"))
	 0)
	(t
	 (when (or log-generalize*
		   log-insert*)
	   (log-message (list "---------------------------------~%"))
	   (log-message (list "Template Beliefs:~%~S~%Actual Beliefs:~%~S~%~%"
			      (mapcar
			       #'instantiate-listform
			       (significance-threshold (funcall (first qs)
								template)))
			      (mapcar
			       #'instantiate-listform
			       (significance-threshold (funcall (first qs)
								actual))))))
	 (when (or dbg-generalize*
		   dbg-insert*)
	   (format t "Template Beliefs:~%~S~%Actual Beliefs:~%~S~%~%"
		   (mapcar #'instantiate-listform
			   (significance-threshold (funcall (first qs)
							    template)))
		   (mapcar #'instantiate-listform
			   (significance-threshold (funcall (first qs)
							    actual))))
	   (break))
	 (if (or (equalp (make-significance)
			 (funcall (first qs) template))
		 (equalp (make-significance) (funcall (first qs) actual)))
	     (consistent? template actual (rest qs) 2)
	     (let (code)
	       (setq code
		     (mequal (significance-threshold
			      (funcall (first qs) template))
			     (significance-threshold
			      (funcall (first qs) actual))))
	       (when (or dbg-generalize*
			 dbg-insert*)
		 (format t "Template and Actual are consistent on ~S.~%"
			 (car qs))
		 (break))
	       (consistent? template actual (rest qs) code))))))

(defun remove-my-person-from-template-match (template actual)
  (when (or log-generalize*
	    log-insert*)
    (log-message (list "******************************~%"))
    (log-message (list "*****Hack Remove my-person****~%"))
    (log-message (list "******************************~%~%")))
  
  (let (my-person-temp my-person-actual bindings)
    (setq my-person-temp
	  (car (member 'my-person template
		       :test #'(lambda (x bel)
				 (eq x (cinstance-name bel))))))
    (setq my-person-actual
	  (car (member 'my-person actual
		       :test #'(lambda (x bel)
				 (eq x (cinstance-name bel))))))
    (when (or log-generalize*)
      (log-message (list "my-person in temp:~%~S~%" my-person-temp))
      (log-message (list "my-person in actual:~%~S~%" my-person-actual)))
    (cond((and my-person-temp my-person-actual)
	  (setq bindings
		(remove-duplicates
		 (caar (match-bconds (mapcar #'instantiate-listform
					     (remove my-person-temp template
						     :test 'equal))
				     (remove my-person-actual actual
					     :test 'equal)
				     nil
				     nil
				     t
				     nil))
		 :test 'equal))
	  (when (or log-generalize*)
	    (log-message (list "New Candidate Bindings: ~S~%" bindings)))
	  (cond ((and (skill-eq (nth 3 (instantiate-listform my-person-temp))
				(nth 3 (instantiate-listform my-person-actual))))
		 (when (or log-generalize*)
		   (log-message (list "My-person actions are equal in both instances.~%"))
		   (log-message (list "Candiate Bindings set is valid.~%")))
		 (push (cons (nth 1 (instantiate-listform my-person-temp))
			     (nth 1 (instantiate-listform my-person-actual)))
		       bindings))
		(t
		 (log-message (list "My-person actions are not equal in both instances. Failing.~%"))
		 nil)))
	 (t
	  (when (or log-generalize*)
	    (log-message (list "Failing.~%")))
	  nil))))

#| Test to see if the template instantiate the actual and the actual
   instantiates the template |#

;; template = template episode beliefs to perform consistency
;; actual = episode beliefs I'm trying to insert to perform consistency on
(defun two-way-instantiate? (template actual)
  (when (or log-generalize*
	    log-insert*)
    (log-message (list "******************************~%"))
    (log-message (list "*****Two Way Instantiate?*****~%"))
    (log-message (list "******************************~%~%"))
    (log-message (list "Teplate Episode Beliefs:~%~S~%"
		       (mapcar #'instantiate-listform template)))
    (log-message (list "Actual Episode Beliefs:~%~S~%"
		       (mapcar #'instantiate-listform actual))))
  (let (temp-2-actual-bindings
	actual-2-temp-bindings
	removed-person
	bconds-res)
    (setq bconds-res
	  (match-bconds (mapcar #'instantiate-listform template)
			actual
			nil
			nil
			t
			nil))
    (loop
       named iterator
       for res in bconds-res
       with match-code = 0
       do
	 (when (or log-generalize*
		   log-insert*)
	   (log-message (list "Iterating of match-bconds results.~%")))
	 (setq temp-2-actual-bindings
	       (remove-duplicates (car res) :test 'equal))
	 (setq actual-2-temp-bindings
	       (remove-duplicates
		(caar (match-bconds (mapcar #'instantiate-listform actual)
				    template
				    nil
				    nil
				    t
				    nil
				    t))
		:test 'equal))
	 (when (or (null temp-2-actual-bindings)
		   (member nil temp-2-actual-bindings))
	   (when (or log-insert*
		     log-generalize*)
	     (log-message (list "template to actual bindings are null.~%"))
	     (log-message (list "Attempting to remove my-person from beliefs.~%")))
	   (setq temp-2-actual-bindings
		 (remove-my-person-from-template-match template actual))
	   (setq actual-2-temp-bindings
		 (mapcan #'(lambda (binding)
			     (when (not (listp (first binding)))
			       (list binding)))
			 actual-2-temp-bindings)))
	 (when (or log-generalize*
		   log-insert*)
	   (log-message (list "Template to Actual Bindings:~%~S~%"
			      temp-2-actual-bindings))
	   (log-message (list "Actual to Template Bindings:~%~S~%"
			      actual-2-temp-bindings)))
	 (when (or dbg-generalize*
		   dbg-insert*)
	   (format t "Template to Actual Bindings:~%~S~%" temp-2-actual-bindings)
	   (format t "Actual to Template Bindings:~%~S~%" actual-2-temp-bindings)
	   (break))
	 (cond
	   ;; Exact match
	   ((and (not (null temp-2-actual-bindings))
		 (not (null actual-2-temp-bindings))
		 (equal temp-2-actual-bindings actual-2-temp-bindings))
	    (when (or log-generalize*
		      log-insert*)
	      (log-message (list "---------------------------------~%"))
	      (log-message (list "Exact Match Found in (two-way-instantiate?).~%Returning 1.~%")))
	    (when (or dbg-generalize*
		      dbg-insert*)
	      (format t "Exact Match Found in (two-way-instantiate?).~%Returning 1.~%"))
	    (setq match-code 1))
	   ;; Generalized match
	   ((and
	     (not (null temp-2-actual-bindings))
	     (not (null actual-2-temp-bindings))
	     (every #'(lambda (b)
			(eq (car b) (cdr (assoc (cdr b) temp-2-actual-bindings))))
		    actual-2-temp-bindings)
	     (every #'(lambda (b)
			(eq (car b) (cdr (assoc (cdr b) actual-2-temp-bindings))))
		    temp-2-actual-bindings))
	    (when (or log-generalize*
		      log-insert*)
	      (log-message (list "---------------------------------~%"))
	      (log-message (list "Generalized Match Found in (two-way-instantiate?).~%Returning 2.~%")))
	    (when (or dbg-generalize*
		      dbg-insert*)
	      (format t "Generalized Match Found in (two-way-instantiate?).~%Returning 2.~%"))
	    (setq match-code 2))
	   ;; Total failure
	   (t
	    (when (or log-generalize*
		      log-insert*)
	      (log-message (list "---------------------------------~%"))
	      (log-message (list "Total Failure in (two-way-instantiate?).~%Looping.~%")))
	    (when (or dbg-generalize*
		      dbg-insert*)
	      (format t "Total Failure in (two-way-instantiate?).~%Looping.~%"))
	    (setq match-code 0)))
       when (not (= match-code 0))
       do
	 (when (or log-generalize*
		   log-insert*)
	   (log-message (list "Match found. Exiting loop.~%")))
	 (return-from iterator match-code)
       finally
	 (when (or log-generalize*
		   log-insert*)
	   (format t "Total Failure in (two-way-instantiate?).~%Returing 0.~%"))
	 (return-from iterator 0))))

(defun mequal (template actual)
#|
  (when dbg-generalize*
    (format t "Template Beliefs:~%~S~%~%"
	    (mapcar #'instantiate-listform template))
    (format t "Actual Beliefs:~%~S~%"
	    (mapcar #'instantiate-listform actual))
    (break))
  |#
  (when (or log-insert*)
    (log-message (list "******************************~%"))
    (log-message (list "*******Checking Equality******~%"))
    (log-message (list "******************************~%~%")))
  (if (and (null template) (null actual)) t
      (cond
	((cinstance-p (first template))
	 (when (and dhm-debug* (not dbg-variableize*))
	   (format t "(first template) is a cinstance~%"))
	 (cond ((= (length (mapcar #'instantiate-listform template))
		   (length (mapcar #'instantiate-listform actual)))
		(two-way-instantiate? template actual))
	       (t
		(when (or log-insert*)
		  (log-message (list "Number of beliefs are different. Equality test Failed.~%~%")))
		0)))
	(t
	 (notany #'null (loop
			   for explanation1 in template
			   for explanation2 in actual
			   collect 
			     (notany #'null 
				     (loop
					for state1 in (mapcar #'first explanation1)
					for state2 in (mapcar #'first explanation2)
					collecting (and
						    (eq (length state1) (length state2))
						    (match-bconds (mapcar #'(lambda (bel)
									      (instantiate-listform bel))
									  state1)
								  state2
								  '()
								  '()))))))))))

#| Initialize the episodic long term memory |#

;; dbg-variablize = flag for printing debug statments in variablization code
;; dbg-explain = flag for printing debug statements in explanation generation
(defun init-eltm (&optional
		    (dbg-variableize nil)
		    (dbg-explain nil)
		    (dbg-insert nil)
		    (dbg-generalize nil))
  (cond (dbg-variableize (setq dbg-variableize* t))
	(dbg-explain (setq dbg-explain* t))
	(dbg-insert (setq dbg-insert* t))
	(dbg-generalize (setq dbg-generalize* t)))
  (delete-log)
  (setq listforms* '())
  (setq numeric-atts* 0)
  (setf (getf eltm* :episodes)
	(cons (gensym "EPISODE-")
	      (make-episode :significant-relation (make-significance)
			    :causal-event (make-significance)
			    :count 0)))

  (setf (getf eltm* :cache)
	(make-cache :states '()
		    :actions '()
		    :episodes '()
		    :bindings '()))
  ;(eltm-to-pdf)
  eltm*)

#| Modify the contents of the 'frequency-tracker' tree |#

; epi-nodes = list of children
; p = parent of the list of children
; item = item to modify with
; listform, type, instances = case specifiers
(defun modify-tree (epi-nodes p item listform type instance)
  (cond 
    ((and (not (null listform)) (null type) (null instance))
     (let* ((l (make-epi-node :name (head-listform (cinstance-head item))))
	    (existing (first (member (epi-node-name l) epi-nodes :key #'epi-node-name :test #'equal))))
       (if existing
	   (progn
	     (modify-tree (epi-node-children existing) existing item listform 'types '()))
	   (progn
	     (setq epi-nodes (reverse (cons l (reverse epi-nodes))))
	     (modify-tree (epi-node-children l) l item listform 'types '()))))
     epi-nodes)
    ((and (not (null listform)) (not (null type)) (null instance))
     (let* ((concept-id (cinstance-id item))
	    (concept (first (member concept-id 
				    cltm* 
				    :test #'(lambda (id concept)
					      ;(format t "Concept-id: ~S~%My id: ~S~%"
					;	      (concept-id concept) id)
					      (if (eq (symbol-name (concept-id concept)) 
						      (symbol-name id))
						  t)))))
	    (key (mapcar #'(lambda (ele)
			     (if (listp (third ele))
				 (first (third ele))))
			 (concept-elements concept)))
	    (ty (make-epi-node :name key))
	    (existing (first (member (epi-node-name ty) 
				     (epi-node-children p) 
				     :key #'epi-node-name 
				     :test #'equal))))
       
       ; Add belief type to types level
       (if existing
	   (progn
	     (modify-tree (epi-node-children existing) existing item listform type 'instance))
	   (progn
	     (setf (epi-node-children p) (reverse (cons ty (reverse (epi-node-children p)))))
	     (setf (epi-node-parent ty) p)
	     (modify-tree (epi-node-children ty) ty item listform type 'instance)))
       (epi-node-children p)))
    ((and (not (null listform)) (not (null type)) (not (null instance)))
     ; Add this belief's head to the instances
     (let* ((head (cinstance-head item))
	    (i (make-epi-node :name (deep-copy-cinstance item)))
	    (existing (first (member (epi-node-name i) 
				     (epi-node-children p) 
				     :key #'epi-node-name 
				     :test #'(lambda (i exist)
					       (head-eq (cinstance-head i) 
							(cinstance-head exist)))))))
       (if existing
	   (progn
	     (setf (epi-node-count existing)
		   (+ 1 (epi-node-count existing)))
	     (adjust-counts (epi-node-parent existing)))
	   (progn
	     (setf (epi-node-count i)
		   (+ 1 (epi-node-count i)))
	     (setf (epi-node-parent i) p)
	     (setf (epi-node-children p) (reverse (cons i (reverse (epi-node-children p)))))
	     (adjust-counts (epi-node-parent i))))
       (epi-node-children p)))
    (t (error "Invalid arangement of arguments"))))

(defun adjust-counts (epi-node)
  (if (null epi-node)
      0
      (progn
	(setf (epi-node-count epi-node)
	      (reduce #'+ (mapcar #'(lambda (child)
				      (epi-node-count child))
				  (epi-node-children epi-node))))
	(adjust-counts (epi-node-parent epi-node)))))

(defun head-eq (h1 h2)
  (if (and (equal (head-name h1) (head-name h2))
	   (equal (head-bindings h1) (head-bindings h2)))
      t))

#| Record events in the cache. When significant relations appear, save the episode.
   Assume that there is only one surprising belief in the environment at a time. |#

;; action = action that was taken in the environment. Could be agent or observed
;; state = state of the environment (belief statements)
(defun register-env (&optional state action)
  ;; Record state and actions into the cache
  (let ((cache (getf eltm* :cache))
	(location (instantiate-listform (first (loop
					   for belief in state
					   when (equal 'at (head-name (cinstance-head belief)))
					   collect belief))))
	(significant-names '()))
    (let ((tree (cdr (assoc location listforms* :test #'(lambda (loc list) (equal (first list) loc)))))) 
    ;; Update the frequency tracker tree (listforms*)
    (mapcar #'(lambda (belief) 
		(setq tree (modify-tree tree '() belief 'listform '() '())))
	    state)
    ;;(setq tree (cons location tree))
    (if (null (assoc location listforms* :test #'(lambda (loc list) (equal (first list) loc))))
	(setq listforms* (cons (cons (list location 1) tree) listforms*))
	(setf (nth (position (assoc location listforms* :test #'(lambda (loc list) (equal (first list) loc))) listforms*) listforms*)
	      (cons (list location (incf (second (first (assoc 
							 location 
							 listforms* 
							 :test #'(lambda (loc list) 
								   (equal (first list) loc)))))))
		    tree))))

    ;(break) 
    (setf (cache-actions cache)
	  (reverse (cons (cons action cycle*) 
			 (reverse (cache-actions cache)))))
    (setf (cache-states cache)
	  (reverse (cons state 
			 (reverse (cache-states cache)))))

    ; remove the belief if it is not surprising
    (let ((surprised
	   (list (remove 'nil (mapcar #'(lambda (bel)
					  (if (surprising bel location)
					      bel
					    '()))
				      state)))
;		 (surprise-by-absence state location (get-important-objs)))
	   )
	  (significance-functions '(significance-threshold significance-absence)))
      (if (or (not (null (first surprised)))
	      (not (null (second surprised))))
	  (let ((q (make-episode :significant-relation 
				 (make-significance :threshold (first surprised)
						    :absence (second surprised)) 
				 :causal-event 
				 (make-significance 
				  :threshold
				  (explain (first surprised)
					   (cache-states cache)
					   (cache-actions cache))
				  
				  :absence 
				  (mapcar #'(lambda (s)
					      '()
					      ;; let explanations = (explain s '() ...)
					      #|(if t ;; <- explanation fails
						  (mapcar #'(lambda (state action)
							      (list state (list (car action))))
							  (cache-states cache)
							  (cache-actions cache)))
					      OR
					      (explain s
					      '()
					      (cache-states cache)
					      (cache-actions cache)
					      '())|#)
					  (second surprised)))
				 :count 1)))
	    ;; I don't think i need this. What's supposed to happen here is that the explanation code points to the spot in the state where the sig events happen.
	    #|
	    (mapcar #'(lambda (significance-function)
			(if (null (first (funcall significance-function 
						  (episode-causal-event q))))
			    (progn
			      (setf (episode-state-sequences q)
				    (cache-states cache))
			      (setf (episode-action-sequences q)
				    (cache-actions cache)))))
		    significance-functions) |#
	    (let ((id (gensym "EPISODE-")))
	      ; insert new episode into episodic memory
	      (insert-episode (list (getf eltm* :episodes)) 
			      (cons id q) 
			      '(episode-significant-relation 
				;;episode-causal-event
			      ))
	      ;; We can do [(episode-id . pointer to episode)] and assoc for next/prev
	      (setf (cache-episodes cache) 
		    (reverse (cons id (reverse (cache-episodes cache)))))))))))

(defun get-important-objs ()
      (loop for problem in gstm* nconcing
	 (loop for goal in (problem-goals problem) nconcing
	      (cdr (goal-objective goal)))))

#| Retreive an episode from the eltm |#

; goal = belief
; eltm = episodic long term memory
; sig-type = determines if this a significance of threshold, absence or repetition
(defun retreive-helper (goal eltm sig-type) 
  ; match-bconds ensures that the the concept exists
  (let* ((ptr '())
	 (goal-listform (head-listform (cinstance-head goal)))
	 (ep-sigs (funcall sig-type (episode-significant-relation (cdr eltm))))
	 (bindings '())
	 (found (if (notevery 
		     'null 
		     (mapcar #'(lambda (sig) 
				 (car (bmatches goal-listform sig bindings))) 
			     ep-sigs))
		    t
		    '())))
    (when found
      (if (notevery #'null 
		    (mapcar 
		     #'(lambda (sig)
			 (let ((bindings (bmatches (instantiate-listform goal) sig bindings)))
			   (if (null (car bindings))
			       '()
			       (notany #'null (mapcar #'(lambda (binding)
							  (cond
							    ((variablep (car binding))
							     (variablep (cdr binding)))
							    (t
							     (eq (car binding) (cdr binding)))))
						      (cdr bindings)))))) 
		     ep-sigs))
	  (nconc (list eltm) (list ptr) (list t))
	  (nconc (list eltm) (list ptr) (list '()))))))

#| Solve an impasse using steps from a similar situation |#

; eltm = episodic long term memory
; goal = Goal I'm looking to achieve
; cur = current state
(defun impasse-resolve (eltm goal cur)
  ; find a state that contains the goal
  (let ((forest (retreive eltm goal 'significance-threshold))
	(plans '()))
    (format t "Forest:~%~S~%" forest)
    ;(break)
    (mapcar #'(lambda (tree)
		(let* ((goal-position 
			(position goal 
				  (significance-threshold 
				   (episode-significant-relation (cdar tree))) 
				  :test #'equal))
		       (explanation (nth goal-position 
					 (significance-threshold 
					  (episode-causal-event (cdar tree)))))
		       ;; Find a state in the explanation that's similar to cur
		       (start-seq (loop
				       named starter
				       for state-action in explanation
				       do
					 (let ((state (first state-action)))
					   (loop
					      for bel in cur
					      do (if (notany #'null
							     (match-bconds
							      (list (head-listform (cinstance-head bel)))
							      state
							      '()
							      '()))
						     (return-from starter
						       (nthcdr (position state-action 
									 explanation
									 :test 'equal)
							       explanation))))))))
		  (format t "Goal Position: ~S~%Explanation States:~%~S~%Current State:~%~S~%Start Seq: ~S~%"
			  goal-position (loop
					   for state in (mapcar #'first explanation)
					   collecting
					     (loop
						for bel in state
						collect (instantiate-listform bel))) 
			  (mapcar #'(lambda(bel)
				      (head-listform (cinstance-head bel))) cur)
			  start-seq)
		  ;(break)
		  (when (not (null start-seq))
		    (setq plans
			  (cons
			   (loop
			      for action in (mapcar #'second start-seq)
			      for state in (mapcar #'first start-seq)
			      nconcing
				(action-apply action 
					      (first 
					       (member (first action) sltm* 
						       :key 'sclause-head 
						       :test #'(lambda (x y)
								 (equal (first y) x))))
					      cstm*))
			   plans))
		    (return-from impasse-resolve (setq hplan* (reverse (first plans)))))
		  (format t "I'm stuck~%")))
	    forest)))
		  
#| Maps action across all applable beliefs in the current state|#

; action = action to map
; sclause = skill definintion of action
; cur = current state to analyze
(defun action-apply (action sclause cur)
  (mapcar #'(lambda (applicable)
	      (list (first action) 
		    (cdr (assoc (second (head-listform (cinstance-head applicable)))
				(head-bindings (cinstance-head applicable)))))) 
	  (loop
	     for bel in cur 
	     when (member (head-listform (cinstance-head bel)) 
			  (sclause-elements sclause) :key 'third :test #'(lambda (bel ele)
									   (equal (first bel)
										  (first ele))))
	     collect bel)))

#| Retreive an episode from the eltm using a cue|#

; eltm = episodic long term memory
; q = que to look for in eltm...can 
; sig-type = matching on threshold, absence, or repetition?
(defun from-que-retreive (eltm q sig-type)
    (let* ((forest (retreive eltm q sig-type)))
      (list forest '())))

#| Retreive and episode from the episodic long term memory |#

; eltm = episodic long term memory
; goal = goal i'm trying to find in the episode
; sig-type = determines if this a significance of threshold, absence or repetition
(defun retreive (eltm goal sig-type)
  (let* ((queue '())
	(temp eltm)
	(match '())
	(match-forest 
	 (remove-if #'(lambda (tree)
			(null (car tree)))
		    (loop 
		       while (not (null temp)) 
		       do
		       ;; test/visit epi-node
			 (setq match (retreive-helper goal temp sig-type))
			 (if (or (and (not (null (car match)))
				      (null (third match)))
				 (equalp (make-significance) 
					 (episode-significant-relation (cdr temp))))
			     (progn
			       (mapcar #'(lambda (sub)
					   (setq queue 
						 (reverse (cons sub (reverse queue)))))
				       (episode-sub-episodes (cdr temp)))))
			 (setq temp (car queue))
			 (setq queue (cdr queue))
		       collecting (if (third match) match)))))
    match-forest))

(defun compute-effect (effect)
  (mapcar #'(lambda (arg)
	      (cond ((listp arg)
		     (eval arg))
		    (t
		     arg)))
	  effect))

#| Compute how many goals the skill yielded from init-state |#

;; goals = goal list to match
;; effects = intention effects
;; bindings = intention bindings
(defun goals-in-effects (goals effects bindings)
  ;; effects may have (_ is _) format
  ;; effects may contain numerals
  (let ((flat-effects
	 (mapcar #'(lambda (f)
		     (if (listp (third f))
			 (compute-effect (subst-bindings bindings (third f)))
			 (compute-effect (subst-bindings bindings f))))
		 effects)))
    (when dbg-explain*
      (format t "Intention Bindings: ~S~%Instantiated Flat Effects: ~S~%Goals: ~S~%" bindings flat-effects goals)
      ;(break)
      )
    (loop
       for goal in goals
       when (member goal flat-effects
		    :test #'(lambda(g member)
			      (loop
				 for goal-element in g
				 for member-element in member
				 with true = t
				 when (and (not (eq goal-element
						    member-element))
					   (not (variablep member-element)))
				 do (return '())
				 finally (return true))))
       collect goal)))

#| Find the primitive skill that was fired in init |#

;; goals = effects skill should have
;; init-state = initial state
;; partial = partial primitive skill
;; state-bindings = bindings that are true in the current state
(defun match-skill (goals init-state partial state-bindings)

  ;; ADD AN ARGUMENT HERE CALLED STATE-BINDINGS THAT IS THE MATCH-BCONDS OF
  ;; INIT-STATE WITH ITSELF. THAT WAY I CAN GET THE EFFECT BINDINGS AS WELL
  
  ;; remove all skills that are not primitive, not consistent with observations
  (let ((prev-best-goal-covering-size 0)
	(candidate '())
	(goal-listforms (mapcar #'(lambda (goal)
				    (head-listform (cinstance-head goal)))
				goals)))
    (when dbg-explain*
      (trace unify))
    (mapcan #'(lambda (skill)
		(format t "Skill:~%~S~%" skill)
		(let (bindings)
		  (do ((head (car (sclause-actions skill))
			     (car (sclause-actions skill)))
		       (partial-skill (car partial) (car partial)))
		      ((or (null head)
			   (null partial-skill)))
		    (let ((binds (unify head partial-skill)))
		      (if (null binds)
			  (return (setq bindings '()))
			  (setq bindings (union binds bindings)))))
		  #|(loop
		     for head in (sclause-actions skill)
		     for partial-skill in partial
		     with binds = (unify partial-skill head bindings)
		     if (null binds)
		     do
		       (return (setq bindings '()))
		     else
		     do
		       (setq bindings (union binds bindings)))|#
		  (format t "Bindings: ~S~%" bindings)
		  (when (and (null (sclause-subskills skill))
			     bindings
			     (= (length (sclause-actions skill))
				(length partial))
			     (> (length
				 (goals-in-effects goal-listforms
						   (sclause-effects skill)
						   state-bindings))
				prev-best-goal-covering-size))
		    (format t "yo~%")
		    (setq prev-best-goal-covering-size
			  (length (intersection goal-listforms
						(subst-bindings
						 bindings
						 (sclause-effects skill)))))
		    (setq candidate (subst-bindings bindings skill))))
		(format t "~%"))
	    sltm*)
    (when dbg-explain*
      (untrace unify))
    ;; return the skill and uncovered goals
    (list candidate (set-exclusive-or (intersection goal-listforms
						    (sclause-effects candidate))
				      goal-listforms))))

#| Find all the skills that contain skill-so-far as subskill |#

;; skill-so-far = skill in subskill of higher level skill
(defun get-high-level-skill-dep (skill-so-far)
  (mapcan #'(lambda (skill)
	      (let ((skill-pos (search skill-so-far
				       (sclause-subskills skill)
				       ;; Test ignores disjunctive skills
				       ;; Problem..I don't know how to
				       ;; solve that yet
				       :test #'(lambda (x y)
						 (equal (first x) 
							(first y))))))
		(when (and (null (sclause-actions skill))
			   skill-pos
			   (notany 'null (mapcar #'unify-match
						 (subseq
						  (sclause-subskills skill)
						  skill-pos)
						 skill-so-far)))
		  (list skill))))
	  sltm*))

#| Find if skill so far matches exactly one of the candidates |#

;; candidates = canonical skills
;; skill-so-far = observed skill
(defun high-level-match? (candidates skill-so-far)
  (loop
     for candidate in candidates
     when (notany 'null (mapcar #'unify-match
				(sclause-subskills candidate)
				skill-so-far))
     do
       (return candidate)))

#| Retrieve the primitive skill that was performed by ICARUS |#

;; goals = effects skill should have
;; actions = actions seen so far
;; states = state sequence
;; skill-so-far = partial skill that matches action sequence
(defun get-prim-skill (goals actions states skill-so-far)
  (when dbg-explain*
    (trace match-skill))
  (let (partial-prim-skill
	partial-state-seq
	(rev-actions (reverse actions))
	(rev-states (rest (reverse states)))) ;; get the state before last action
    (do ((action (car rev-actions) (car rev-actions))
	 (state (car rev-states) (car rev-states)))
	((or (null action)
	     (null state)))
      (push action partial-prim-skill)
      (format t "Partial Primitive Skill: ~S~%" partial-prim-skill)
      (push state partial-state-seq)
      (let* ((state-bindings (match-bconds (mapcar #'instantiate-listform state)
					   state
					   '()
					   '()))
	     (res (match-skill goals state partial-prim-skill state-bindings)))
	(when res
	  (when dbg-explain*
	    (untrace match-skill))
	  (push (first res) skill-so-far)
	  (return (list (set-exclusive-or actions partial-prim-skill
					  :test 'equal)
			(set-exclusive-or states partial-state-seq
					  :test 'equal)
			skill-so-far
			(second res))))))
    #|(loop
       for action in (reverse actions)
       for state in (rest (reverse states)) 
       collect action into partial-prim-skill
       collect state into partial-state-seq
       with state-bindings = (match-bconds (mapcar #'instantiate-listform state)
					   state
					   '()
					   '())
       with res = (match-skill goals state partial-prim-skill state-bindings)
       when (first res) ;; skill should be instantiated
       ;; return left over actions
       ;; return left over states
       ;; return the skill so far
       ;; return uncovered goals
       do
	 (when dbg-explain*
	   (untrace match-skill))
	 (push (first res) skill-so-far)
	 (return (list (set-exclusive-or actions partial-prim-skill :test 'equal)
		       (set-exclusive-or states partial-state-seq :test 'equal)
		       skill-so-far
		       (second res)))) |#))
  
#| Infinately abstract over skills to retrieve highet-level last skill |#

;; goals = effects skill should have
;; actions = actions seen so far
;; states = state sequence
;; skill-so-far = partial skill that matches action sequence
;; candidates = higher level skills that contain skill-so-far as subskill
(defun get-last-skill-2 (goals actions states skill-so-far candidates)
  (cond ((null candidates) (list skill-so-far states actions goals))
	(t
	 (when dbg-explain*
	   (trace get-prim-skill))
	 (let* ((res (get-prim-skill goals actions states skill-so-far))
		(candidates (get-high-level-skill-dep (third res)))
		(higher-level-skill (high-level-match? candidates (third res))))
	   (when dbg-explain*
	     (untrace get-prim-skill))
	   (cond (higher-level-skill
		  (setq skill-so-far '())
		  (push higher-level-skill skill-so-far)
		  (when dbg-explain*
		    (format t "Skill so far:~%~S~%" skill-so-far))
		  (setq candidates (get-high-level-skill-dep skill-so-far))
		  (when dbg-explain*
		    (format t "Candidates:~%~S~%~%" candidates))
		  (get-last-skill (fourth res)
				  (first res)
				  (second res)
				  skill-so-far
				  candidates))
		 (t
		  (get-last-skill (fourth res)
				  (first res)
				  (second res)
				  (third res)
				  candidates)))))))

;; states = state sequence
;; ints = intention sequence
;; int = current intention
;; goals = goals to explain
(defun get-last-skill (states ints goals)
  (when dbg-explain*
    ;(break)
    )
  (let (new-states
	new-ints
	new-goals
	c-int)
    (when dbg-explain*
      (format t "Intentions:~%~S~%" ints)
      ;(break)
      )
    (loop
       named outer
       for int in ints
       for state in states
       with pos = 0
       do
	 (incf pos)
	 (when dbg-explain*
	   (format t "Intention:~%~S~%State:~%~S~%Pos: ~d~%" int state pos)
	   ;(break)
	   )
	 (when (or (not (null int))
		   (null state))
	   (cond ((not (null int))
		  (setq c-int int)
		  (setq new-states (reverse (subseq states pos)))
		  (setq new-ints (reverse (subseq ints pos)))
		  (return-from outer '()))
		 ((null state)
		  (setq new-states (list (car states)))
		  (setq new-ints (list (car ints)))
		  (return-from outer '())))))
    (if (not (null c-int))
	(setq new-goals
	      (set-exclusive-or
	       (goals-in-effects goals
				 (sclause-effects (intention-operator c-int))
				 (intention-bindings c-int))
	       goals))
	(setq new-goals goals))
    (when dbg-explain*
      (format t "New Goals: ~S~%" new-goals)
      (break))
   
    (list (if (null c-int)
	      '()
	      (let ((inst-sclause (make-sclause
				   :head
				   (subst-bindings (intention-bindings c-int)
						   (sclause-head
						    (intention-operator c-int)))
				   :id
				   (intention-id c-int)
				   :elements
				   (subst-bindings (intention-bindings c-int)
						   (sclause-elements
						    (intention-operator c-int)))
				   :tests
				   (sclause-tests (intention-operator c-int))
				   :conditions
				   (sclause-conditions (intention-operator c-int))
				   :effects
				   (subst-bindings (intention-bindings c-int)
						   (sclause-effects
						    (intention-operator c-int)))
				   :actions
				   (subst-bindings (intention-bindings c-int)
						   (sclause-actions
						    (intention-operator c-int))))))
		#|(mapcar #'(lambda (element)
			    (if (listp (third element))
				(third element)
				element))
		(sclause-elements inst-sclause))|#
		inst-sclause))
	  new-states
	  new-ints
	  new-goals)))
#| Generate an explanation for how the goals became true |#

;; goals = goals to explain
;; states = state sequence
;; ints = intention sequence
;; sol = solution, built up in a piecemeal fashion
(defun explain-goals (goals states ints sol)
  ;; base case implies we try to explain as much as we can rather than
  ;; just giving up when we can't explain the whole trace
  (when dbg-explain*
    (break))
  (cond ((or (null goals)
	     (null states))
	 (when dbg-explain*
	   (format t "Returning from EXPLAIN-GOALS:~S~%~%" sol)
	   (break))
	 sol) 
	(t
	 (when dbg-explain*
	   (trace get-last-skill))
	 (let* ((rev-ints (reverse ints))
		(rev-states (reverse states))
		(res (get-last-skill rev-states
				     rev-ints
				     goals))
		(last-skill (first res))
		(new-states (second res))
		(new-ints (third res))
		(uncovered-goals (fourth res)))
	   
	   (when dbg-explain*
	     (untrace get-last-skill))
	   ;; When last skill add skill 
	   (when (and last-skill (not (= (length goals)
					 (length uncovered-goals))))
	     ;; Add the last skill to the solution
	     ;; Outer list is for compatiblity.
	     ;; In the old days we had an explanation for each belief.
	     ;; Now we have one explanation all significant events.
	     ;; That means that rather than having a list of lists
	     ;; i.e. an explanation for each sig event. We just have one list.
	     ;; Old code will get refactored..just later though.
	     (push (list (list #|(mapcar #'(lambda (ele)
				     (if (listp (third ele))
					 (third ele)
					 ele))
		    (sclause-elements last-skill))|#
		    (reverse (first states))
		    (sclause-head last-skill)))
		   sol))
	   
	   ;; Try to cover the uncovered goals
	   (explain-goals uncovered-goals
			  new-states
			  new-ints
			  sol)))))

#| Explains how a set of beliefs came to be |#

; goal-instances = significant events I'm trying to explain
; states = state trace
; ints = intention trace
(defun explain (goal-instances states ints)
  ;; I might have to do positives and negatives for goal explanation
  (let* ((goals (mapcar #'(lambda(goal-instance)
			    (when (cinstance-p goal-instance)
			      (csubst-bindings (cinstance-bindings goal-instance)
					       (head-listform (cinstance-head goal-instance)))
			      goal-instance))
			goal-instances)))
    (when dbg-explain* (trace explain-goals)
	  (explain-goals (mapcar #'instantiate-listform goals) states (mapcar #'first ints) '()))))
  
(defun care ())


#| Detect all the coincidences that occur with a belief |#

; eltm = episodic long term memory
; q = Literal that should be found to do virtual sensing on
(defun get-coincidences (listforms q dummy)
  (let* ((denom (second (first (assoc q listforms 
				     :test #'(lambda (cue list) (equal (first list) cue)))))) 
	(context (cdr (assoc q listforms :test #'(lambda (cue list) (equal (first list) cue)))))
	(counts (loop 
		   for listform in context
		   nconcing 
		     (loop
			for type in (epi-node-children listform)
			nconcing
			  (loop
			     for head in (epi-node-children type)
			     collect (epi-node-count head)))))
	 (heads (loop 
		   for listform in context
		   nconcing 
		     (loop
			for type in (epi-node-children listform)
			nconcing
			  (loop
			     for head in (epi-node-children type)
			     collect (epi-node-name head)))))
	 (probs (mapcar #'(lambda (head count)
			    (cons head (/ count denom)))
			heads counts)))
    #|(format t "~%~%Probs:~%~S~%"
	    (mapcar #'(lambda (prob)
			(cons (instantiate-listform (car prob)) (cdr prob)))
		    probs))|#
    
    (remove-if-not #'(lambda (item)
		       (> .5 (cdr item)))
		   probs)))

#| Detect all the coincidences that occur with a belief |#

; eltm = episodic long term memory
; q = Literal that should be found to do virtual sensing on
(defun get-coincidences-2 (eltm q sig-type)
  (let ((instantiated (deep-copy-cinstance q)))
    (setf (head-listform (cinstance-head instantiated))
	  (instantiate-listform q))
    (let* ((forest (retreive eltm q sig-type))
	  (denominator (reduce '+ (sort (mapcar #'(lambda (ep)
						    (episode-count (cdar ep)))
						forest) #'>)))
	  (beliefs (loop
		      for ep in forest
		      nconcing (funcall sig-type (episode-significant-relation (cdar ep)))))
	   (seen '()))
      (mapcar #'(lambda (belief)
		  (if (not (member belief seen :key 'car :test 'equal))
		      (setq seen 
			    (cons (list 
				   belief 
				   (/ (reduce '+  
					      (mapcar 
					       #'(lambda (ep)
						   (if (member belief 
							       (funcall 
								sig-type 
								(episode-significant-relation 
								 (cdar ep))) 
							       :test 'equal)
						       (episode-count (cdar ep))
						       0))
					       forest))
				      denominator))
				  seen))))
	      beliefs)
      (mapcar 'first (remove-if #'(lambda (item)
				    (< (second item) .5))
				seen)))))
      #|(let ((applicable-sigs-per-ep (remove 'nil (mapcar #'(lambda (applicable-ep)
							     (if (episode-p (cdar applicable-ep)) 
								 (funcall sig-type
									  (episode-significant-relation (cdar applicable-ep)))
								 '()))
							 (car res)))))
	(reduce 'append (mapcar #'(lambda (applicable-sigs)
				    (coincidences applicable-sigs))
				applicable-sigs-per-ep)))))) |#

(defun coincidences (applicable-sigs)
  (remove '()
	  (mapcar #'(lambda (bel)
		      (if (member t 
				  (mapcar 
				   #'(lambda (binding)
				       (if (variablep (cdr binding))
					   '()
					   t))
				   (head-bindings (cinstance-head bel)))
				  :test 'equal)
			  bel
			  '()))
		  applicable-sigs)))

#| Returns with T if belief from the state is surprising |#

; b = belief to be examined
; q = location info
(defun surprising (b q)
  ; Check frequency of belief at listform, type and instance level
  (let* ((b-listform (head-listform (cinstance-head b)))
	 (b-instance (cinstance-head b))
	 (concept-id (cinstance-id b))
	 (concept (first (member concept-id 
				 cltm* 
				 :test #'(lambda (id con)
					   (if (eq (symbol-name (concept-id con)) 
						   (symbol-name id))
					       t)))))
	 (b-type (mapcar #'(lambda (ele)
			     (if (listp (third ele))
				 (first (third ele))))
			 (concept-elements concept)))
	 (listform (first (member b-listform (cdr (assoc q listforms* :test #'(lambda (loc list) (equal (first list) loc)))) 
				  :key #'epi-node-name 
				  :test #'equal)))
	 (types (epi-node-children listform))
	 (type (first (member b-type types 
			      :key #'epi-node-name 
			      :test #'equal)))
	 (instances (epi-node-children type))
	 (instance (first (member b-instance instances 
				  :key #'epi-node-name 
				  :test #'(lambda (x y)
					    (head-eq x (cinstance-head y)))))))
    ; Eventually, you'd want to check against what your action models are telling you
    (or (<= (epi-node-count instance) episodic-learning-threshold*) 
	(<= (epi-node-count type) episodic-learning-threshold*) 
	(<= (epi-node-count listform) episodic-learning-threshold*))))

#| Returns with T if the state is missing an expected belief |#
; st = state we are observing
; q = location q
; s = names of objects we need to complete the goal
(defun surprise-by-absence (st q s) '())
(defun surprise-by-absence-2 (st q s)
  (let ((expected (get-coincidences listforms* q 'significance-absence)))
    (remove-if 'null (mapcar #'(lambda (exp)
				 (if (and (member (cadr (instantiate-listform (car exp))) s 
						  :test 'equal) 
					  (not (member (cinstance-head (car exp)) st 
						       :key 'cinstance-head 
						       :test 'head-eq)))
				     (car exp)))
			     expected))))

#| Simulate storing perceptions from ICARUS cycle in episodic memory |#

(defun epi-run ()
  (register-env  (infer cltm* 
			(list '(block B1 ^x 0 ^y 0 ^len 2 ^height 2)
			      '(block B2 ^x 0 ^y 2 ^len 2 ^height 2)
			      '(block B3 ^x 0 ^y 4 ^len 2 ^height 2)
			      '(block B4 ^x 0 ^y 6 ^len 2 ^height 2)
			      '(table t1 ^x 0 ^y 0 ^len 20)
			      ;;'(expert exp1 action nil)
			      ;;'(hand H1 status empty)
			      )
			'())
		 '(*open ?shoes))
  (break)
  (register-env  (infer cltm* 
			(list '(block A1 ^x 0 ^y 0 ^len 2 ^height 2)
			      '(block A2 ^x 0 ^y 2 ^len 2 ^height 2)
			      '(block A3 ^x 0 ^y 4 ^len 2 ^height 2)
			      '(block A4 ^x 0 ^y 6 ^len 2 ^height 2)
			      '(table t1 ^x 0 ^y 0 ^len 20)
			      ;;'(expert exp1 action nil)
			      ;;'(hand H1 status empty)
			      )
			'())
		 '(*open ?moo))
  (break)
  (register-env  (infer cltm* 
			(list '(block B5 ^x 0 ^y 0 ^len 2 ^height 2)
			      '(block B6 ^x 0 ^y 2 ^len 2 ^height 2)
			      '(table t1 ^x 0 ^y 0 ^len 20)
			      ;;'(expert exp1 action ((*vertical-move B5 14)))
			      ;;'(hand H1 status B5)
			      )
			'())
		 '(*open ?kitty))
  (break)
  (register-env  (infer cltm* 
			(list '(block B2 ^x 0 ^y 0 ^len 2 ^height 2)
			      '(block B3 ^x 0 ^y 2 ^len 2 ^height 2)
			      '(table t1 ^x 0 ^y 0 ^len 20)
			      ;;'(expert exp1 action ((*vertical-move B2 14)))
			      ;;'(hand H1 status B2)
			      )
			'())
		 '(*open ?cow))
  (break)
  (register-env  (infer cltm* 
			(list '(block B4 ^x 0 ^y 0 ^len 2 ^height 2)
			      '(block B5 ^x 0 ^y 2 ^len 2 ^height 2)
			      '(table t1 ^x 0 ^y 0 ^len 20)
			      ;;'(expert exp1 action ((*horizontal-move B5 14)))
			      ;;'(hand H1 status B5)
			      )
			'())
		 '(*open ?laptop))
  (break)
  (register-env  (infer cltm* 
			(list '(block B1 ^x 0 ^y 0 ^len 2 ^height 2)
			      '(block B3 ^x 0 ^y 2 ^len 2 ^height 2)
			      '(table t1 ^x 0 ^y 0 ^len 20)
			      ;;'(expert exp1 action ((*horizontal-move B1 14)))
			      ;;'(hand H1 status B1)
			      )
			'())
		 '(*open ?pole))
  (break)
  (register-env  (infer cltm* 
			(list '(block B6 ^x 0 ^y 0 ^len 2 ^height 2) 
			      '(block B3 ^x 0 ^y 2 ^len 2 ^height 2)
			      '(table t1 ^x 0 ^y 0 ^len 20)
			      ;;'(expert exp1 action ((*horizontal-move B3 14)))
			      ;;'(hand H1 status B3)
			      )
			'())
		 '(*open ?table))
  ;; I want to trace match-conds generalization code
  ;;(setq dhm-debug* t)
  ;;(setq dbg-variableize* t)
  (break)
  (register-env  (infer cltm* 
			(list '(block B5 ^x 0 ^y 0 ^len 2 ^height 2)
			      '(block B1 ^x 0 ^y 2 ^len 2 ^height 2)
			      '(table t1 ^x 0 ^y 0 ^len 20))
			'())
		 '(*open ?table))
  ;;(setq dhm-debug* '())
  ;;(setq dbg-variableize* '())
  (break)
  (register-env  (infer cltm* 
			(list '(block B3 ^x 0 ^y 0 ^len 2 ^height 2)
			      '(table t1 ^x 0 ^y 0 ^len 20))
			'())
		 '(*open ?dinner))
  (break))
  ;(eltm-to-pdf)
  ;listforms*)


(defun eltm-to-pdf ()
  (let ((ep (getf eltm* :episodes)))
    (with-open-file (eltm-file "eltm.dot"
			       :direction :output
			       :if-exists :overwrite
			       :if-does-not-exist :create)
      (format eltm-file "digraph G {~%")
      (pdf-helper ep '() eltm-file)
      (format eltm-file "}")))
  (sb-ext:run-program
   "dot"
   (list "-Tpdf" "eltm.dot" "-o" "eltm.pdf")
   :search t
   :wait '()))


(defun instantiate-listform (belief)
  (subst-bindings (cinstance-bindings belief)
		  (head-listform (cinstance-head belief))))

(defun pdf-helper (eps parent stream)
  (let* (;;(*print-right-margin* 10)
	 (id (subseq (symbol-name (car eps)) 8))
	 (ep (cdr eps))
	 (sigs (make-significance :threshold
				  (mapcar #'(lambda (belief)
					(instantiate-listform belief))
					  (significance-threshold 
					   (episode-significant-relation ep)))
				  :absence
				  (mapcar #'(lambda (belief)
					      (instantiate-listform belief))
					  (significance-absence 
					   (episode-significant-relation ep)))))
	 (causals
	  (make-significance :threshold
			     (mapcar #'(lambda (explanation)
					 (mapcar #'(lambda (state action)
						     (cons
						      (mapcar
						       #'instantiate-listform
						       state)
							   (list action)))
						 (mapcar #'first explanation)
						 (mapcar #'second explanation)))
				     (significance-threshold
				      (episode-causal-event ep)))
			     :absence
			     (mapcar #'(lambda (explanation)
					 (mapcar #'(lambda (state action)
						     (cons
						      (mapcar
						       #'instantiate-listform
						       state)
							   (list action)))
							 (mapcar #'first explanation)
							 (mapcar #'second explanation)))
					     (significance-absence 
					      (episode-causal-event ep)))))
	 (count (episode-count ep))
	 ;;(*print-right-margin* 110)
	 )
    ;print ep
    (format stream "~S [shape=record, label=\"{~S~%|~S~%|~S}\"];~%" id sigs causals count)
    (if parent
	(format stream "~S -> ~S;~%" parent id))

    ;visit children
    (mapcar #'(lambda (e)
		(pdf-helper e id stream))
	    (episode-sub-episodes ep))))      

#|
TESTS

(retreive (getf eltm* :episodes) (first (significance-threshold (episode-significant-relation (cdr (first (episode-sub-episodes (cdr (getf eltm* :episodes)))))))) 'significance-threshold)
|#
