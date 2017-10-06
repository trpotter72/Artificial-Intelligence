
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Expermental results code
(defparameter nodes-explored* 0)
(defparameter nodes-failed* 0)

(defun get-results ()
  (time (grun))
  (format t "~%~%;;;;;;;;;;;;;;;;~%")
  (format t "No of nodes explored: ~a~%" nodes-explored*)
  (format t "No of nodes failed: ~a~%" nodes-failed*)
  (format t ";;;;;;;;;;;;;;;;~%~%"))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Code for Icarus Rewrite
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Functions called from RUN-AUX
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun select-active-problem ()
  (when (not active-problem*)
    (loop with unsatisfied-problem-found? = nil
	  for problem in gstm*
	  while (not unsatisfied-problem-found?)
	  do
	  (when (not (problem-satisfied-with-bindings problem))
	    (setq active-problem* problem)
	    (setq unsatisfied-problem-found? t)))))
	
(defun solve (active-problem executing-intention) 
  ;; Expect Problem to be an active Problem that is not satisfied, and executing-intention is an "Executing Intention" or NIL
  (print-problem-and-exec-intent active-problem executing-intention)

  (cond	(executing-intention ; If there is an intention currently executing
	 (execute-one-step executing-intention))

	;; execution changes world and belief state, so pieces of problem tree may be based on false
	;; assumptions.  This flushes elements of problem solver state to improve system behavior.
	#|((and (just-finished-executing) 
	      active-problem
	      (not remembered))
	 (impass-resolve (getf eltm* :episodes))
	 (setq remembered t))|#
	((and (just-finished-executing) active-problem
	      (equal problem-solver-enabled* 'meansends))
	 ;Check if the active problem is achieved
	 (let ((flag t))
	   (loop named goal-checker
		 for goal in (csubst-bindings
			      (problem-bindings active-problem)
			      (problem-objectives active-problem))
		 when (not (goal-literal-satisfied? goal))
		 do
		 (setq flag nil)
		 (return-from goal-checker))
	   (if flag
	       (let ((higher-level-intention (problem-i-parent active-problem)))
		 (if higher-level-intention
		     (setq active-problem* (intention-problem-parent
					    higher-level-intention))
		   (setq active-problem* nil)))
	 ;Choi:This below prevents the means-ends problem solver to continue
	 ;     working on next level up subgoal when achieved the current one.
	 ;     Encapsulating it inside an IF statement.
	     (reset-problem-solver-state
	      (get-top-level-problem active-problem)))))
	((and (just-finished-executing) active-problem
	      (equal problem-solver-enabled* 'planner))
	 (if hplan*
	     (hardcode-intentions)
	     ;(set-first-intention-from-hplan hplan*)
	   (reset-problem-solver-state (get-top-level-problem active-problem))))
	((and active-problem
	      (equal problem-solver-enabled* 'meansends))
	 (backward-chain-problem-solve active-problem))
	((and active-problem
	      (equal problem-solver-enabled* 'planner))
	 ;(format t "~&In planner subroutine~&")
	 (if (null hplan*)
	    (setq hplan* 'mock-plan) 
	    ;(forward-search)
	     (hardcode-intentions)
	     ;(set-first-intention-from-hplan hplan*)
	     ))
	(problem-solver-enabled*
	 (setf halt* t)
	 (print "No active problem and no executing intention"))
	(t
	 (format t "~&Exiting SOLVE without any work~&"))))

(defun set-first-intention-from-hplan (hplan)
  (let* ((first (caar hplan*))
	 (skill (task-skill first))
	 (sclause (car (member (skill-id skill) sltm*
			       :key 'sclause-id :test 'equal)))
	 (first-intention
	  (make-intention
	   :id (sclause-id sclause)
	   :head (task-head first)
	   :operator sclause
;	   :conditions (sclause-conditions sclause)
; Dongkyu:
; as soon as I enable the below, the execution breaks because
; target-satisfied? function thinks the target is satisfied
;	   :effects (sclause-effects sclause)
	   :bindings (caar
		      (match-pconds (sclause-elements sclause)
				    pstm*
				    nil
				    (remove 'unknown (task-bindings first)
					    :key 'cdr :test 'equal)))
	   :subskills (sclause-subskills sclause)
	   :remaining-subskills (sclause-subskills sclause)
	   :action (sclause-actions sclause))))
    (format t "~&Setting intention from hplan*: ~A"
	    (task-head first))
    (setf (problem-intention (car gstm*)) first-intention)
    (set-executing-intention first-intention)
    (pop hplan*)))

(defun hardcode-intentions ()
  (let* ((first (car david-plan*))
	 (sclause (first (member first sltm* 
				  :key #'sclause-head
				  :test 'equal)))
	 (to-open (car boxes*))
	 (bindings (caar (match-pconds (sclause-elements sclause)
				 (remove-if #'(lambda (percept)
						(if (and (eq 'BOX (car percept))
							 (not (eq to-open (second percept))))
						    t))
					    pstm*)
				 '()
				 '())))
	 (intention (make-intention
		     :id (sclause-id sclause)
		     :head (subst-bindings bindings first)
		     :operator sclause
;	   :conditions (sclause-conditions sclause)
; Dongkyu:
; as soon as I enable the below, the execution breaks because
; target-satisfied? function thinks the target is satisfied
;	   :effects (sclause-effects sclause)
		     :bindings (caar
				(match-pconds (sclause-elements sclause)
					      pstm*
					      nil
					      (remove 'unknown bindings
						      :key 'cdr :test 'equal)))
		     :subskills (sclause-subskills sclause)
		     :remaining-subskills (sclause-subskills sclause)
		     :action (sclause-actions sclause))))
    (format t "~&Setting intention from david-plan*: ~A"
	    (subst-bindings bindings first))
    (setf (problem-intention (car gstm*)) intention)
    (set-executing-intention intention)
    (pop david-plan*)
    (pop boxes*)))


(defun report-toplevel-problem-satisfied ()
  (format t "~%**************************************************")
  (format t  "~%All Top-Level Goals of Active Problem Satisfied~%")
  (format t "**************************************************~%"))

(defun report-problem-solved (problem)
  (format t "~&Bindings satisfy all goals in problem: ~A"
	  (csubst-bindings (problem-bindings problem) (problem-objectives problem))))

(defun just-finished-executing ()
  ;; detects a transition from executing intention to none
  (and (null executing-intention*)
       prior-executing-intention*
       (equal (second prior-executing-intention*) (1- cycle*))))

(defun reset-problem-solver-state (top-level-problem)
  ;; eliminate elements of problem solver state so
  ;; they refresh in the current world and belief state

  (cond (flush-problem-tree*
	 (format t "~&Flushing problem tree")
	;; this approach blows away the current problem and replaces it with a fresh version 
	 (let ((new (make-problem-from-clauses (problem-objectives top-level-problem))))
	   (replace-problem top-level-problem new)
	   (push top-level-problem problem-tree-history*)
	   (setq active-problem* new)))))

(defun print-problem-and-exec-intent (active-problem executing-intention)
  (unless pat-trace* 
    (format t "~&Call to SOLVE with problem/intention-stack:"))
  (when problem-solver-enabled*
    (print-problem-intention-stack (reverse (get-problem-intention-stack active-problem)))
  (cond (active-problem
	 (format t "~&~%  Active Problem:")
	 (pprint-problem active-problem))
	  (t (format t "~%  Active Problem: NIL"))))
  (cond (executing-intention
	 (if pat-trace*
	     nil ;(format t "~%Active Intention:")     ; moved to when intention set
	     (format t "~&~%  Executing Intention:"))
	 (if pat-trace*
	     nil ;(pprint-pat-intention executing-intention)  ; moved to  when intention set
	     (pprint-intention executing-intention)))
	(t (if pat-trace*
	       nil ; (format t "~%Active Intention: None")   ;moved to when intention set
	       (format t "~&~%  Executing Intention: NIL")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Problem functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstruct problem
  id					; how are id's generated (for goals, skills, etc.)?
  goals
  objectives
  pos-objectives
  neg-objectives			; note that these still include the NOT's
  bindings
  binding-map                           ;; used to track variable names, which are altered to deconflict naming spaces
  bindings-selected?
  intention
  focus
  i-parent
  target-goals                          ;; goals that have been set as targets for the selected intention with the matching order preserved
  successful-subskill-executions
  failure-context-list
  disjunctive-goal-list?              ;;denotes if a problem has a set of disjunctive goals.
  visited-states                      ;;stores a list of visited states. Instantiated in the top level problem only.
  repeating-intentions)                   ;;stores a list of repeating intentions. Instantiated in the top level problem only.
 

(defstruct goal 
  objective 
  sfailed 
  cfailed 
  problem 
  status)

(defun pprint-problem-objectives (problem) (pprint-problem problem :selectors '(:objectives)))

(defun pprint-problem (problem
		       &key
		       (subst-bindings? t)
		       (indent "    ")
		       (selectors '(:objectives :bindings :bindings-selected?
				    :focus :target-goals :intention)))
  (when problem
    (format t "~%~aPROBLEM:" indent)
    (loop for selector in selectors
	  do
	  (case selector
	    (:objectives (format t "~%~a  Objectives: ~a" 
				 indent
				 (if subst-bindings? 
				     (csubst-bindings (problem-bindings problem)
						     (problem-objectives problem))
				     (problem-objectives problem))))
	    (:bindings (format t "~%~a  Bindings: ~a" 
			       indent
			       (problem-bindings problem)))
	    (:bindings-selected?  (format t "~%~a  Bindings-selected?: ~a" 
					  indent
					  (problem-bindings-selected? problem)))
	    (:target-goals (format t "~%~a  Target-Goals: ~a" 
				   indent
				   (if subst-bindings?
				       (csubst-bindings (problem-bindings problem)
						       (problem-target-goals problem))
				       (problem-target-goals problem))))
	    (:focus (format t "~%~a  Focus: ~a" 
			    indent
			    (if subst-bindings? 
				(csubst-bindings (problem-bindings problem)
						(problem-focus problem))
				(problem-focus problem))))
	    (:intention (let ((short-intention (if (problem-intention problem)
						   (intention-head (problem-intention problem))
						   nil)))
			  (format t "~%~a  Intention: ~a" 
				  indent
				  (if subst-bindings? 
				      (csubst-bindings (problem-bindings problem)
						      short-intention)
				      short-intention))))))))

(defun collect-pos-conditions (condition-list)
  (loop for condition in condition-list
     unless (eql (first condition) 'not)
     collect condition))

(defun collect-neg-conditions (condition-list)
  (loop for condition in condition-list
     when (eql (first condition) 'not)
     collect condition))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Skill and Intention functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defstruct sclause
;;   head				
;;   id 
;;   percepts				; only for primitive skills ?
;;   tests
;;   conditions
;;   effects
;;   subskills				; NIL for primitive skills
;;   action				; only a single action (but could be a lisp function to call sequence of actions)
;;   )

(defstruct intention
  id                   ; id of the skill this intention was instantiated from
  operator             ;; definition of the skill (or concept) associated with this intention
  problem-parent
  execution-i-parent
  head                 ; similar to old head, but does not have to match a concept.  Used for calling subskills
  conditions
  effects
  targets	       ; subset of effects serving as terminating conditions (desired effects)
  bindings
  subskills            ; list of subskill calls.  NIL for primitive intentions/skills
  remaining-subskills  ; remaining subskills to execute (previous already succeeded)
  execution-flag       ; T for executing, NIL otherwise
  action               ; only used for primitive intentions.  Then is a single action that can be executed.
  action-executed?     ; used to check if action has been executed at least once
  percepts	       ; only for primitive intentions to use to get bindings for action call
  tests
  successful-subskill-executions
  failed-subskill-executions
 )

;; (defmacro create-skills (&rest skills)
;;   `(let ((skills (quote ,skills))
;; 	 result)
;;      (do ((next-skill (car skills) (car skills)))
;; 	 ((null skills)
;; 	  (setq sltm* (append sltm* (reverse result))) nil)
;;        (push (create-skill-clause next-skill) result)
;;        (pop skills))))

;; (defun create-skill-clause (skill)
;;   (let ((head (car skill))
;; 	(id nil)
;; 	(percepts nil)
;; 	(tests nil)
;; 	(conditions nil)
;; 	(effects nil)
;; 	(subskills nil)
;; 	(action nil))
;;     (pop skill)				; get rid of head, rest is alternating :key <spec> pairs
;;     (do ((next-field (car skill) (car skill))
;; 	 (next-spec (cadr skill) (cadr skill)))
;; 	((null skill)
;; 	 (cond ((null id) (setq id (incf id-count*))))
;; 	 (make-sclause :head head
;; 		       :id id
;; 		       :percepts percepts
;; 		       :tests tests
;; 		       :conditions conditions
;; 		       :effects effects
;; 		       :subskills subskills
;; 		       :action (quote-constants action))) ; check out / find out what this does 
;;       ;; do keywords need to be quoted below?
;;       (cond ((eq next-field ':percepts)(setq percepts next-spec))
;; 	      ((eq next-field ':id)(setq id next-spec))
;; 	      ((eq next-field ':tests)(setq tests next-spec))
;; 	      ((eq next-field ':conditions)(setq conditions next-spec))
;; 	      ((eq next-field ':effects)(setq effects next-spec))
;; 	      ((eq next-field ':subskills)(setq subskills next-spec))
;; 	      ((eq next-field ':action)(setq action next-spec))
;; 	      (t (print-error next-field "field" "skill")))
;;       (setq skill (cddr skill)))))

;; this version keeps the clauses and bindings separate.  It only subsitutes bindings into primitive
;; structures (actions, percepts, and tests).
(defun create-intention (skill bindings &optional execution-flag)
  (let ((new-intention (make-intention :id (sclause-id skill)
				       :operator skill
				       :head (sclause-head skill)
				       :conditions  (sclause-conditions skill)
				       :effects  (sclause-effects skill)
				       :bindings bindings
				       :subskills  (sclause-subskills skill)
				       :execution-flag execution-flag
				       :action (norvig-qsubst-bindings bindings (sclause-actions skill))
				       :action-executed? nil
				       :percepts (csubst-bindings bindings (sclause-elements skill))
				       :tests  (csubst-bindings bindings (sclause-tests skill)))))
    (setf (intention-remaining-subskills new-intention)
	  (intention-subskills new-intention))
    (setf (intention-targets new-intention)
	  (intention-effects new-intention)) ; the default is for targets to be all of effects
    new-intention))

(defun create-dummy-intention-for-concept-chaining (head conditions bindings concept)
  (let ((result nil))
    (cond ((not (eq (car head) 'not))
	   (make-intention :id nil
			   :operator concept
			   :head head
			   :conditions conditions
			   :effects  head
			   :bindings bindings
			   :subskills nil
			   :execution-flag nil
			   :action nil
			   :action-executed? nil
			   :percepts nil
			   :tests  nil))
	  (t
	   
	   ;;Get bound negations to avoid illegal bindings of negated conditions.
	   (setq result (get-chainable-negations (csubst-bindings bindings conditions)))
	   (setq conditions (car result))
	   (setq bindings (append bindings (cadr result)))

	   (make-intention :id nil
			   :head head
			   :conditions conditions
			   :effects  head
			   :bindings bindings
			   :subskills nil
			   :execution-flag nil
			   :action nil
			   :action-executed? nil
			   :percepts nil
			   :tests  nil)))))

(defun primitive-intention? (intention)
  (null (intention-subskills intention)))

(defun pprint-intention (intention
			 &key
			 (subst-bindings? t)
			 (indent "    ") 
			 (selectors '(:head :bindings :subskills
				      :remaining-subskills :conditions
				      :effects :targets :action)))
  (when intention
    (format t "~%~aINTENTION:" indent)
    (loop for selector in selectors
       do
       (case selector
	 (:head (format t "~%~a   Head: ~a" indent
				(if subst-bindings? 
				    (csubst-bindings (intention-bindings intention)
						    (intention-head intention))
				    (intention-head intention))))
	 (:bindings (format t "~%~a   Bindings: ~a" indent
			    (intention-bindings intention)))
	 (:subskills (format t "~%~a   Subskills: ~a" indent
			     (if subst-bindings? 
				 (csubst-bindings (intention-bindings intention)
						 (intention-subskills intention))
				 (intention-subskills intention))))
	 (:remaining-subskills (format t "~%~a   Remaining-Subskills: ~a" indent
				       (if subst-bindings? 
					   (csubst-bindings (intention-bindings intention)
							   (intention-remaining-subskills intention))
					   (intention-remaining-subskills intention))))
	 (:conditions (format t "~%~a   Conditions: ~a" indent
			      (if subst-bindings? 
				  (csubst-bindings (intention-bindings intention)
						  (intention-conditions intention))
				  (intention-conditions intention))))
	 (:effects  (format t "~%~a   Effects: ~a" indent
			    (if subst-bindings? 
				(csubst-bindings (intention-bindings intention)
						(intention-effects intention))
				(intention-effects intention))))
	 (:targets  (format t "~%~a   Targets: ~a" indent
			    (if subst-bindings? 
				(csubst-bindings (intention-bindings intention)
						(intention-targets intention))
				(intention-targets intention))))
	 (:action  (format t "~%~a   Action: ~a" indent
			   (if subst-bindings? 
			       (norvig-qsubst-bindings (intention-bindings intention)
						(intention-action intention))
			       (intention-action intention))))))))

(defun pprint-pat-intention (intention
			     &key
			     (subst-bindings? t)
			     (indent "    ") 
			     (selectors '(:head :bindings :conditions
					  :subskills :action :effects)))
  (when intention
    (unless pat-trace*
      (format t "~%~aINTENTION:" indent))
    (loop for selector in selectors
       do
       (case selector
	 (:head (format t "~%~a   Head: ~a" indent
			(if subst-bindings? 
			    (csubst-bindings (intention-bindings intention)
					    (intention-head intention))
			    (intention-head intention))))
	 (:bindings (format t "~%~a   Bindings: ~a" indent
			    (intention-bindings intention)))
	 (:subskills (when (intention-subskills intention)
		       (format t "~%~a   Subskills: ~a" indent
			       (insert-caret (- (length (intention-subskills intention))
						(length (intention-remaining-subskills intention)))
					     (if subst-bindings? 
						 (csubst-bindings (intention-bindings intention)
								 (intention-subskills intention))
						 (intention-subskills intention))))))
	 (:remaining-subskills (format t "~%~a   Remaining-Subskills: ~a" indent
				       (if subst-bindings? 
					   (csubst-bindings (intention-bindings intention)
							   (intention-remaining-subskills intention))
					   (intention-remaining-subskills intention))))
	 (:conditions (format t "~%~a   Conditions: ~a" indent
			      (if subst-bindings? 
				  (csubst-bindings (intention-bindings intention)
						  (intention-conditions intention))
				  (intention-conditions intention))))
	 (:effects  (format t "~%~a   Effects: ~a" indent
			    (if subst-bindings? 
				(csubst-bindings (intention-bindings intention)
						(intention-effects intention))
				(intention-effects intention))))
	 (:targets  (format t "~%~a   Targets: ~a" indent
			    (if subst-bindings? 
				(csubst-bindings (intention-bindings intention)
						(intention-targets intention))
				(intention-targets intention))))
	 (:action (when (intention-action intention)
		    (format t "~%~a   Action: ~a" indent
			    (if subst-bindings? 
				(norvig-qsubst-bindings (intention-bindings intention)
						 (intention-action intention))
				(intention-action intention)))))))))

(defun insert-caret (pos list)
  (append (subseq list 0 pos)
	  (list '-->)
	  (subseq list pos)))

(defun set-executing-intention (intention)
  (setf prior-executing-intention* (list executing-intention* cycle*)) ;; keep the history for detecting transitions
  (setf executing-intention* intention)
  (cond (intention
	 (setf (intention-execution-flag intention) t)
	 (cond (pat-trace* 
		(format t "~%Setting Current Intention:")
		(pprint-pat-intention intention)
		;(format t "~%Setting Executing Intention to be: ~a"
		;          (intention-head-with-bindings intention)))
		)
	       (t
		(format t "~%Setting Executing-Intention* to be:")
		(pprint-intention intention))))
	(t (unless pat-trace*  
	     (format t "~%Setting Executing-Intention* to be: NIL")))))


       

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Matching Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; predicate -- T if satisfied with any bindings
(defun goal-literal-satisfied? (goal-literal)
  (car (goal-literal-satisfied goal-literal)))

;;; returns (flag . bindings)
(defun goal-literal-satisfied (goal-literal)
  ;;; SATISFIED function defined in holdover.lisp
  (satisfied goal-literal cstm*))

;; substitutes given bindings, and returns (flag . new-bindings) form for attempted match
(defun goal-literal-satisfied-with-bindings (goal-literal bindings)
  (goal-literal-satisfied
   (csubst-bindings bindings goal-literal)))


;; doesn't make sense for negative literals
(defun find-all-match-bindings (pos-goal-literal cstm)
  ;; like satisfied-positive, but finds all match bindings
  (loop for belief in cstm
     for match-result = (bmatches pos-goal-literal belief nil)
     when (first match-result)
     collect
     (rest match-result)))

;; returns a list of all possible bindings that satisfy the literals.
;; this takes literals in any order (it separates the positive and negative bindings)
(defun find-all-match-bindings-for-literals (literals start-bindings cstm)
  (find-all-match-bindings-for-sorted-literals (collect-pos-conditions literals)
					       (collect-neg-conditions literals)
					       start-bindings
					       cstm))

;; returns a list of all possible bindings that satisfy the literals.
;;; assume already divided into pos and neg lists
(defun find-all-match-bindings-for-sorted-literals (pos-literals neg-literals start-bindings cstm)
  (cond ((null pos-literals)
	 (if (loop for neg-literal in (csubst-bindings start-bindings neg-literals)
		always
		(first (satisfied neg-literal cstm)))
	     (list start-bindings)
	     nil))
	(t
	 (loop for add-bindings in (find-all-match-bindings (csubst-bindings start-bindings
									    (first pos-literals))
							    cstm)
	    append
	    (find-all-match-bindings-for-sorted-literals (rest pos-literals) 
							 neg-literals
							 (append add-bindings start-bindings)
							 cstm)))))

;; version of next function that presorts pos and neg literals
;; Returns T or NIL
(defun exists-match-bindings-for-literals? (literals start-bindings cstm)
  (exists-match-bindings-for-sorted-literals? (collect-pos-conditions literals)
					      (collect-neg-conditions literals)
					      start-bindings
					      cstm))

;; Quicker function to check if pos and neg literals are satisfied
;;   Returns T or NIL
;;   Stops when first match (if any) is found
(defun exists-match-bindings-for-sorted-literals? (pos-literals neg-literals start-bindings cstm)
  (cond ((null pos-literals)
	 (loop for neg-literal in (csubst-bindings start-bindings neg-literals)
	    always
	    (first (satisfied neg-literal cstm))))
	(t
	 (loop for add-bindings in (find-all-match-bindings (csubst-bindings start-bindings
									    (first pos-literals))
							    cstm)
	    thereis
	    (exists-match-bindings-for-sorted-literals? (rest pos-literals) 
							neg-literals
							(append add-bindings start-bindings)
							cstm)))))

;; Checks for the satisfaction of a problem using the bindings within the problem. Returns T or nil.
;; This function does not extend the problem bindings.
(defun problem-satisfied-with-bindings (problem)
  (exists-match-bindings-for-sorted-literals? (problem-pos-objectives problem)
					      (problem-neg-objectives problem)
					      (problem-bindings problem)
					      cstm*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Partial Matching Functions
;;;  (non-greedy, matching against belief memory as structures)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun find-all-max-size-partial-matches-for-literals (literals start-bindings cstm &optional already-matched-literals)
  (find-all-max-size-partial-matches-for-sorted-literals (collect-pos-conditions literals)
							 (collect-neg-conditions literals)
							 start-bindings
							 cstm
							 already-matched-literals))

(defun find-all-max-size-partial-matches-for-sorted-literals (pos-literals neg-literals start-bindings cstm &optional already-matched-literals)
  (let ((all-partial-matches (find-all-partial-match-bindings-for-sorted-literals pos-literals
										  neg-literals
										  start-bindings
										  cstm
										  already-matched-literals)))
    (loop with max-size-matches = nil
       with max-match-size = 0
       for match-pair in all-partial-matches
       for matched-literals = (first match-pair)
       for match-length = (length matched-literals)
       do
	 (cond ((> match-length max-match-size)
		(setf max-match-size match-length
		      max-size-matches (list match-pair)))
	       ((= match-length max-match-size)
		(push match-pair max-size-matches)))
       finally
	 (return max-size-matches))))

;; believe this code never runs
(defun find-all-max-size-partial-matches-for-sorted-literals-for-binding-set (pos-literals neg-literals binding-set cstm &optional already-matched-literals)
  (let ((all-partial-matches nil))

    (loop for bindings in binding-set
	  append (find-all-partial-match-bindings-for-sorted-literals pos-literals
								      neg-literals
								      bindings
								      cstm
								      already-matched-literals)
	  into binding-list
	  finally 
	  (setq all-partial-matches binding-list))
    
    (loop with max-size-matches = nil
       with max-match-size = 0
       for match-pair in all-partial-matches
       for matched-literals = (first match-pair)
       for matched-bindings = (or (second match-pair) no-bindings)
       for match-length = (length matched-literals)
       when (and (not (member-failure-context-list? :problem-bindings matched-bindings))
		 (not (violates-binding-constraints? (csubst-bindings matched-bindings
								     (append pos-literals neg-literals)))))
       do
	 (cond ((> match-length max-match-size)
		(setf max-match-size match-length
		      max-size-matches (list match-pair)))
	       ((= match-length max-match-size)
		(push match-pair max-size-matches)))
       finally
	 (return max-size-matches))))

;;; assume already divided into pos and neg lists
;;;  returns list of pairs: ( ( matched-literals-1 bindings-1 ) ( matched-literals-2 bindings-2 ) ....  )
(defun find-all-partial-match-bindings-for-sorted-literals (pos-literals neg-literals start-bindings cstm &optional already-matched-literals)
  (cond ((null pos-literals)
	 (list (list (append already-matched-literals
			     (loop for neg-literal in neg-literals
				for instantiated-neg-literal = (csubst-bindings start-bindings neg-literal)
				when (first (satisfied instantiated-neg-literal cstm))
				collect neg-literal))
		     start-bindings)))
	(t
	 (append (find-all-partial-match-bindings-for-sorted-literals (rest pos-literals) 
								      neg-literals
								      start-bindings
								      cstm
								      already-matched-literals)
		 (loop for add-bindings in (find-all-match-bindings (csubst-bindings start-bindings
										    (first pos-literals))
								    cstm)
		    append
		    (find-all-partial-match-bindings-for-sorted-literals (rest pos-literals) 
									 neg-literals
									 (append add-bindings start-bindings)
									 cstm
									 (cons (first pos-literals)
									       already-matched-literals)))))))

(defun move-negs-to-end (goals negs)
 (cond ((null goals) negs)
       ((eq (caar goals) 'not)
        (move-negs-to-end (cdr goals) (cons (car goals) negs)))
       (t (cons (car goals) (move-negs-to-end (cdr goals) negs)))))

;; Matches a given set of literals with variables with another set. Renamed from get-satisfied.
(defun pattern-match-literals (goals beliefs &optional return-bindings?)
 (let ((result nil)
       (bindings nil))
   (do ((gnext (car goals) (car goals)))
       ((null goals)
        (if return-bindings?
            (list result bindings)
            (csubst-bindings bindings result)))
       (let ((tbindings (pattern-match-literal gnext beliefs bindings)))
         (cond ((not (null tbindings))
                (setq bindings (cdr tbindings))
                (push gnext result))))
       (pop goals))))

;; Matches positive and negative literals seperately. Renamed from match-goal.
(defun pattern-match-literal (goal beliefs bindings)
 (cond ((eq (car goal) 'not)
        (pattern-match-neg-literal (cadr goal) beliefs bindings))
       (t (pattern-match-pos-literal goal beliefs bindings))))

;; Renamed from match-pos-goal
(defun pattern-match-pos-literal (goal beliefs bindings)
 (cond ((null beliefs) nil)
       (t (let ((tbindings (pattern-matcher goal (car beliefs) bindings)))
            (cond ((null (car tbindings))
                   (pattern-match-pos-literal goal (cdr beliefs) bindings))
                  (t tbindings))))))

;; Renamed from match-neg-goal
(defun pattern-match-neg-literal (ngoal beliefs bindings)
 (cond ((null beliefs)
        (cons t bindings))
       (t (let ((tbindings (pattern-matcher ngoal (car beliefs) bindings)))
            (cond ((not (null (car tbindings))) nil)
                  (t (pattern-match-neg-literal ngoal (cdr beliefs) bindings)))))))

;; Same as bmatches but does not require belief structures. Renamed from bmatches-pat.
(defun pattern-matcher (clist elist bindings)
 (cond ((not (eq (length clist) (length elist)))
        (cons nil bindings))
       (t (let ((flag t))
            (do ((c (car clist) (car clist))
                 (e (car elist) (car elist))
                 (b nil nil))
                ((or (null flag) (null clist))
                 (cons flag bindings))
                (cond ((not (variablep c))
                       (cond ((not (equal c e))(setq flag nil))))
                      ((setq b (assoc c bindings))
                       (cond ((not (equal (cdr b) e))
                              (setq flag nil))))
                      (t (push (cons c e) bindings)))
                (pop clist)
                (pop elist))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; EXECUTION routines
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *repeat-macros?* nil)	        ; control whether to fail or allow repeat if macro targets not satisfied at end
(defparameter *complete-macro-execution?* t)	; control whether to require complete execution of macro subskills (or interrupt when targets satisfied?)


(defun execute-one-step (executing-intention)
  (cond ((execution-completed-successfully? executing-intention)
	 ;; modify so in special case of Null Effects, will execute exactly once (both primitive and macro)
	 (let ((current-state (get-current-state cstm*)))
 	   (record-success executing-intention)
 	   (return-to-caller executing-intention) ; should update executing-intention*, transmit new bindings, advance to next subskill

	   ; Choi: Deactivating - does not work with HEAD structures
	   ;       See PATTERN-MATCH-LITERAL
	   ;;Avoid checking for execution loop while popping of to an intention parent.
;	   (when (intention-problem-parent executing-intention)
;	     (cond ((repeated-state? current-state)
;		    (print "Execution loop detected. Storing the current intention-head.")
;		    (setq execution-loop* t)
;		    (store-intention (problem-intention active-problem*)))
;		   (t
;		    (store-state current-state))))
	   ))	
	((primitive-intention? executing-intention)
	 (cond ((ready-to-execute? executing-intention)
		;; this should check conditions, extend bindings
		;; (with percepts as well), and check
		;; if all variables of action-form are bound
		(cond ((execute-action executing-intention) ; instantiate action, evaluate (run),
		       t)				    ; let next cycle check if targets satisfied
		      (t 
		       ;(record-failure executing-intention)   ;; record/save failed intention in caller-intention or problem
		       (abort-execution 
			executing-intention
			(format nil
				"Failed to Execute-action: ~a"
				(norvig-qsubst-bindings (intention-bindings executing-intention)
						 (intention-action executing-intention)))
			))))
	       (t (abort-execution executing-intention "Not ready to execute"))))
	;; Macro intention / execute subskills
	((or (intention-started? executing-intention) ; conditions only need to be satisfied when first started
	     (ready-to-execute? executing-intention)) ; checks conditions and gets bindings
	 (let* ((remaining-subskills (intention-remaining-subskills executing-intention))
		(next-subskill (if remaining-subskills
				   (csubst-bindings (intention-bindings executing-intention)
						   (first remaining-subskills)))))
	   (cond (next-subskill
		  (cond ((call-intention next-subskill executing-intention)
			 t)
			(t
			 ;; call failed
			 (abort-execution executing-intention (format nil
								      "Call to subskill failed: ~a"
								      next-subskill)))))
		 (*repeat-macros?*      ;; only get here if no next subskill and targets not satisfied
		  ;; targets can't be satisfied here (otherwise execution-completed-successfully? would have returned t)
		  ;; (targets-satisfied? executing-intention)    [NOTE: previous line reasoning may not be valid for executing skills w/ "Null Effects",
		  ;;                                                  but in that case expect *repeat-macros?* to be NIL, so still won't get here]
		  (setf (intention-remaining-subskills executing-intention) ; reset to try executing macro again
			(intention-subskills executing-intention)))
		 (t   ;; fail
		  (abort-execution executing-intention "Aborting execution of macro-intention because targets not satisfied")
		  ))))
	(t 
	 (abort-execution executing-intention "Aborting execution of macro-intention because Ready-to-Execute returned NIL")
	 (format t "~%  Intention that was Not Ready-to-execute:")
	 (pprint-intention executing-intention)
	 )))

 ; modify so in special case of Null Effects, will execute exactly once (both primitive and macro)
(defun execution-completed-successfully? (executing-intention)
  (cond ((and (null (intention-effects executing-intention)) 
	      (primitive-intention? executing-intention))
	 ;; new code for primitive intentions with null effects
	 ;; NOTE: problem-solving will never backchain to a skill with no effects!
	 (intention-action-executed? executing-intention))
	(t (and (or (not *complete-macro-execution?*) ; old code for when effects are not empty
		    (null (intention-remaining-subskills executing-intention)))
		(targets-satisfied? executing-intention)))))

(defun record-success (intention)
  (when pat-trace*
    (format t "~%INTENTION COMPLETED SUCCESSFULLY: ~a"
	    (intention-head-with-bindings intention)))
  (let ((i-parent (intention-execution-i-parent intention)))
    (cond (i-parent
	   (push intention
		 (intention-successful-subskill-executions i-parent)))
	  (t
	   (let ((problem-parent (intention-problem-parent intention)))
	     (if problem-parent
		 (push intention (problem-successful-subskill-executions problem-parent))))))))

(defun intention-head-with-bindings (intention)
  (when intention
    (csubst-bindings (intention-bindings intention)
		    (intention-head intention))))

#|(defun record-failure (intention)
  (let ((i-parent (intention-execution-i-parent intention)))
    (cond (i-parent
	   (push intention
		 (intention-failed-subskill-executions i-parent)))
	  (t
	   (let ((problem-parent (intention-problem-parent intention)))
	     (if problem-parent
		 (push intention (problem-failed-subskill-executions problem-parent))))))))|#
  
;; should update executing-intention*, transmit new bindings, advance to next subskill
;; updates executing-intention*, and passes back any new bindings through head
(defun return-to-caller  (satisfied-intention) ; assumes targets verified to be satisfied (so bindings updated)
  (let ((next-subskill-called? nil)
	(i-parent (intention-execution-i-parent satisfied-intention))
	(instantiated-head (csubst-bindings (intention-bindings satisfied-intention)
						   (intention-head satisfied-intention))))
    (cond (i-parent
	   ;; pass back bindings to i-parent
	   (let* ((i-parent-bindings (intention-bindings i-parent))
		  (i-parent-head (csubst-bindings i-parent-bindings
							 (first (intention-remaining-subskills i-parent)))) ; is this right?????
		  (new-bindings-form (unify-match instantiated-head i-parent-head))
		  (full-bindings (append (if (first new-bindings-form)
					     (rest new-bindings-form)
					     nil)
					 i-parent-bindings)))
	     (setf (intention-bindings i-parent)
		   full-bindings))
	   ;; advance to next subskill
	   (pop (intention-remaining-subskills i-parent))
	   ;; when pat-trace* try going directly to next subskill
	   (when (and pat-trace*
		      (intention-remaining-subskills i-parent)
		      ;; also check repeat-macros? and targets ??
		      )
	     (format t "~%Proceeding directly to next subskill of intention: ~a"
		     (intention-head-with-bindings i-parent))
	     (let* ((remaining-subskills
		     (intention-remaining-subskills i-parent))
		    (next-subskill (csubst-bindings (intention-bindings i-parent)
						   (first remaining-subskills))))
	       (call-intention next-subskill i-parent)
	       (setf next-subskill-called? t))))
	  ;; only do the following if there is actually a problem-parent
	  ((intention-problem-parent satisfied-intention)
	   (return-bindings-to-problem-caller satisfied-intention)))
    (unless next-subskill-called?
      (set-executing-intention i-parent))))

;; this is used when the satisfied-intention has no i-parent
(defun return-bindings-to-problem-caller (satisfied-intention)
  (let* ((target-literals (csubst-bindings (intention-bindings satisfied-intention)
					  (intention-targets satisfied-intention)))
	 (problem-parent (intention-problem-parent satisfied-intention))
	 (target-goal-literals (problem-target-goals problem-parent))
	 (match-form			; ( flag . bindings )
	  (unify-match target-literals 
		       target-goal-literals))
	 (match-flag (car match-form))
	 (match-bindings (rest match-form)))
    (cond (match-flag	; unify-match succeeded
	   (setf (problem-bindings problem-parent)
		 (merge-bindings (problem-bindings problem-parent)
				 match-bindings))) ; note: these bindings dominate, if inconsistent
	  (t  ; match failed - shouldn't happen
	   (warn "Unify Match Failed - this shouldn't happen")))))

;; merge bindings when consistent
;;    if inconsistent, use binding from bindings-2
;;      (think "merge bindings-1 into bindings-2, unless inconsistent)
(defun merge-bindings (bindings-1 bindings-2)
  (loop with merged-bindings = bindings-2
     for bindings-1-form in bindings-1
     for var = (car bindings-1-form)
     for value = (cdr bindings-1-form)
     for bindings-2-lookup = (assoc var bindings-2)
     do
       (cond (bindings-2-lookup
	      (cond ((equal value (cdr bindings-2-lookup))
		     ;; consistent and already there - do nothing
		     )
		    (t ;; inconsistent - keep bindings-2 binding
		     (warn "For Var ~a, inconsitent values ~a and ~a, keeping latter"
			   var value (cdr bindings-2-lookup)))))
	     (t				; var not bound in bindings-2
	      (push bindings-1-form 
		    merged-bindings)))
     finally
       (return merged-bindings)))


;; this should verify that conditions match beliefs, and extend bindings appropriately
;; Returns T or NIL
(defun conditions-satisfied? (intention)
  (let* ((bindings (intention-bindings intention))
	 (preconds (csubst-bindings bindings (intention-conditions intention)))
	 (all-match-bindings
	  (find-all-match-bindings-for-literals preconds
						bindings
						cstm*)))
    (cond (all-match-bindings
	   (setf (intention-bindings intention)
		 (random-choose all-match-bindings))
	   t)
	  (t nil))))

;; this should verify that targets match beliefs, and extend bindings appropriately
;; Returns T or NIL
(defun targets-satisfied? (intention)
  (let* ((bindings (intention-bindings intention))
	 (raw-targets (intention-targets intention)))
    (when (exists-match-bindings-for-literals? raw-targets bindings cstm*)
      (let* ((instantiated-targets (csubst-bindings bindings raw-targets))
	     (all-match-bindings
	      (find-all-match-bindings-for-literals instantiated-targets
						    bindings
						    cstm*)))
	(when all-match-bindings
	  (setf (intention-bindings intention)
		(random-choose all-match-bindings)))
	t))))


(defun random-choose (list)
  (nth (random (length list)) list))

(defun variable-free? (form)
  (cond ((variable-p form) nil)
	((atom form) t)
	(t (and (variable-free? (first form))
		(variable-free? (rest form))))))

(defun ready-to-execute? (exec-intent)
  (when (and (intention-execution-flag exec-intent) ; could assume this is always true when called
	     (conditions-satisfied? exec-intent))
    ;(intention-started? exec-intent)
    ;(setf (intention-already-started? exec-intent) T)
    (when (primitive-intention? exec-intent)
      (extend-bindings-with-percepts exec-intent))
    t))

(defun intention-started? (exec-intent)
  (not (eql (intention-remaining-subskills exec-intent)
	    (intention-subskills exec-intent))))


(defun extend-bindings-with-percepts (exec-intent)
  (let* ((bindings (intention-bindings exec-intent))
	 (percepts (csubst-bindings bindings (intention-percepts exec-intent)))
	 (pmatch (match-pconds percepts pstm* nil nil))
	 (add-bindings nil))
    (cond (pmatch
	   (setf add-bindings (first (random-choose pmatch)))
	   (if dgs-debug* (format nil "Additional bindings: ~S~%" add-bindings))
	   (loop for binding-pair in add-bindings
	      when (variable-p (first binding-pair))
	      do
		(push binding-pair bindings)
	      finally
		(setf (intention-bindings exec-intent)
		      bindings))
	   t)
	  (t nil))))

;; predicate - returns T if succeeds, NIL otherwise
(defun execute-action (exec-intent)
  (let ((action-form (norvig-qsubst-bindings (intention-bindings exec-intent)
					     (intention-action exec-intent))))
    (format t "~%Executing Action Form: ~a~%" action-form)
    (cond ((variable-free? action-form)
	   ;if a list of actions
	   (if (listp (car action-form))
	       (mapcar 'eval action-form)
	     (eval action-form))
	   ;; next for null subskills hack - guarantee action gets executed exactly once
	   (setf (intention-action-executed? exec-intent) t)
	   t)
	  (t (format t "~%  Failed because action-form contained unbound variables")
	     nil))))

(defun abort-execution (exec-intent &optional (message "Aborting Execution"))
  (format t "~% ~a" message)
  ;; Need to (unwind-and-record failed intentions)
  (when active-problem*
    (create-and-store-failure-context 
     active-problem*
     :problem-bindings (problem-bindings active-problem*)
;				      (problem-focus active-problem*)
     :operator (intention-operator (problem-intention active-problem*))
     :operator-bindings (intention-bindings (problem-intention active-problem*))))

    ;;Set the bindings to nil to take care of the fact that the system 
    ;;might have executed actions before failing.
    (setf (problem-bindings-selected? active-problem*) nil)
    (setf (problem-bindings active-problem*) nil)
    (set-executing-intention nil))

;; Question: Does a head have to be completely instantiated?
;;      NO -- Free Variables are possible, and can get bound during execution
;; Predicate: return T or NIL. Side effects: try to create-intention for head, link to calling-intention
(defun call-intention (head &optional calling-intention) ; head already has bindings substituted
  (cond (pat-trace*
	 (format t "~%SKILL CALL: ~a " head))
	(t (format t "~%CALLING INTENTION: ~a " head)))
  (let* ((candidate-skills (find-skills-with-name (first head)))
	 (eligible-skills-with-bindings
	  (loop for skill in candidate-skills
	     for skill-head = (sclause-head skill)
	     for binding-form = (unify-match head skill-head)
	     when (and binding-form (first binding-form))
	     collect (cons skill (rest binding-form))))
	 (matching-skills ; list of (skill . bindings) that match conditions of skill
	  (loop for (skill . bindings) in eligible-skills-with-bindings
	     for conditions = (csubst-bindings bindings (sclause-conditions skill))
	     for all-matches = (find-all-match-bindings-for-literals conditions bindings cstm*)
	     when all-matches
	     collect (cons skill (random-choose all-matches)) ; randomly choose one way to sastisfiy conditions
	     ))
	 (chosen-skill-match (if matching-skills
				 (random-choose matching-skills))))
    (cond (chosen-skill-match
      (let* ((skill (first chosen-skill-match))
	     (bindings (rest chosen-skill-match))
	     (new-intention (create-intention skill bindings t)))
	(setf (intention-execution-i-parent new-intention)
	      calling-intention)
	(set-executing-intention new-intention)
	t
	     ))
	  (t (format t "~%CALL TO INTENTION ~a FAILED BECAUSE NO MATCH FOUND" head)))
    ))


(defun find-skills-with-name (skill-name)
  (loop for next-skill in sltm*
     for next-skill-name = (first (sclause-head next-skill))
     when (eql skill-name next-skill-name)
     collect
     next-skill))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; PROBLEM SOLVING (backward-chaining)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun backward-chain-problem-solve (problem)
  (cond
    
    ;; Problem has no bindings, so select them.
    ((null (problem-bindings-selected? problem))
     (cond ((well-formed problem)
	    (print "Selecting bindings.")
	    (select-bindings problem))
	   (t (format t "~&Failing problem because it is not well formed")
	      (create-and-store-failure-context problem :problem-bindings (problem-bindings problem))
	      (backtrack))))
    
    ;;Choi: Here,
    ;;      deal with cases where the problem is already satisfied in the state.
    ;;      This should not happen if SKILL-CHAIN works right.
    
    ;; Problem has no intention, so form one
    (t ;(not (problem-intention problem))
     (let* ((intention (problem-intention problem))
	    (op (if (intention-p intention)
		    (intention-operator intention))))
       (cond ((null op)
	      (terpri)(princ "Selecting an operator")
	      (setq op (select-operator problem))
	      (if debug*
		  (format t "~& Operator returned by select-operator ~A" op))

       ;; if operator represents a concept, create appropriate subproblem via concept chaining
       ;; if operator represents a skill, create subproblem via skill chaining 
	      (cond (op 
		     (if (typep (opmatch-operator op) 'sclause)
			 (skill-chain problem op)
		       (concept-chain problem op)))

	     ;; select-operator failed. 
		    (t

		     (print "Failed to select intention for the current problem with given bindings. Backtracking.")
		     (create-and-store-failure-context problem :problem-bindings (problem-bindings problem))

;	      (create-and-store-failure-context (problem-bindings problem))
		     (setf (problem-bindings problem) nil)
		     (setf (problem-bindings-selected? problem) nil)
		     )))
	     (t
	      (if (typep op 'sclause)
		  (skill-chain problem nil)
		(concept-chain problem nil))))))
    (t
     (warn "You should never be here in backward-chain-problem-solve."))))

(defun skill-chain (problem op)
  (let (intention)
    (cond (op
           ;; produce subordinate intention and problem structure from op
	   (setq intention
		 (create-intention (opmatch-operator op) (opmatch-bindings op)))
	   (setf (intention-problem-parent intention) problem)
	   (setf (problem-intention problem) intention)

	   (print "Skill selected")
	   (pprint-intention intention))
	  ; if the operator selection was already done before
	  (t
	   (setq intention (problem-intention problem))))
    ;;Choi: Execute if all the conditions for the intention are satisfied.
    (let ((flag t))
      (loop named condition-checker
	    for goal in (intention-conditions intention)
	    when (not (goal-literal-satisfied? goal))
	    do
	    (setq flag nil)
	    (return-from condition-checker))
      (cond (flag
	     (set-executing-intention intention))
	    (t
	     (make-problem-from-conditions intention)
	     (incf nodes-explored*))))))

(defun concept-chain (problem op)
  (if op
      (let* ((concept (opmatch-operator op))
	     (bindings (opmatch-bindings op))
	     (intention
	      (create-dummy-intention-for-concept-chaining 
	       (concept-head concept)
	       (concept-relations concept)
	       bindings
	       concept))
	     (goals-matched (opmatch-goals-matched op))
	     (target (if goals-matched (first goals-matched) nil)))

	(setf (intention-problem-parent intention) problem)
	(setf (problem-intention problem) intention)

	(print "Concept selected for chaining")
	(pprint-intention intention)
	(make-problem-from-conditions intention)
	    ;;If chaining off a negative goal, flag the new problem as disjunctive.
	(cond ((and target (equal (length goals-matched) 1))
	       (if (eq (car target) 'not)
		   (setf (problem-disjunctive-goal-list? active-problem*) t)))
	      (t (error (format nil "~&More than one target for concept chaining in opmatch ~A" op)))))
    (make-problem-from-conditions (problem-intention problem)))
  (incf nodes-explored*))
    


;; This function generates maximal match for the list of problem goal-literals and randomly selects one.
;; Returns nil if none of the goal-literals match, (nil . bindings) if there is a partial match and
;; (t . bindings) if all goal literals are matched.
;; This function extends the problem bindings(if any) with the bindings of the chosen  maximal match.
;;    patched 030212 by dgs to return the constant no-bindings in place of nil for positive matches


;; Returns (skill bindings) that meets the heuristic skill selection
;; criterion.  The heuristic considers the skill's match against the environment
;; as well as it ability to achieve goals in the current problem.

;; In more detail, let the number of a skill's effects that match onto unsolved
;; goals, and conditions that match onto current beliefs follow this table:

;; Goals              Conditions         Comment
;;  0                    0              skill is not relevant to goal or situation
;;  0                    <all           skill is not goal relevant and not actionable in situation
;;  0                    all            skill is not goal relevant, but it is actionable now
;;  1+                   0+             skill is goal relevant and may or may not be actionable

;;Select-skill generates and compares the last two sets. As a result, the
;;returned skill is either purely exploratory, or applicable to the goal, most
;;likely after some further problem solving.

;Choi: Iterative sampling does not filter out operators that achieves
;      already satisfied goals. NEED FIX.
(defun select-operator (problem &optional (bind-unchainables? t))
  ;; consider skills and concepts.  Generate their maximal matches against goals and beliefs.
  ;; Heuristically rank the matches, and probabilistically select the best.

  (let ((goal-relevant-skill-seeds nil)   ;; list of opmatch structures 
	(actionable-seeds  nil )          ;; list of opmatch structures
	(goal-relevant-concept-seeds nil) ;; list of opmatch structures
	(maximal-candidates nil)          ;; list of opmatch structures with maximal bindings
	(selected-candidate nil)          ;; the winning opmatch structure

	;; Incorporates bindings from problem. Check if this chases binding chains through vars bound
	;; to vars ***
	(remaining-goals (unsatisfied-goals-for-problem problem)))  

    ;; comment this out on theory that system should always be motivated by the goal, even if
    ;; it is pursuing a bad theory.  That action will change the world, and, because problem solving
    ;; restarts after action, the problem will change.
;;    (setq actionable-seeds (find-goal-irrelevant-actionable-skills remaining-goals))
    ;; (if dgs-debug* (format t "~&Actionable seed candidates: ~A" actionable-seeds))

    ;; Find skills that satisfy >=1 goal clause by collecting skills + bindings that
    ;; unify with any unsatisfied goal in problem, taken one at a time.  Then,
    ;; augment the bindings by matching against both remaining problem goals and
    ;; skill conditions to find maximal binding sets.
   
    ;; loop through skills that are relevant and initialize candidate matches
    (setq goal-relevant-skill-seeds
	  (loop for skill in (skills-relevant-to-goals remaining-goals)
	       collect (create-opmatch skill problem)))
    (if dgs-debug* (format t "~&goal-relevant skill selection seeds: ~A" goal-relevant-skill-seeds))

    ;; find goal-relevant concepts 
    (setq goal-relevant-concept-seeds 
	  (loop for concept in (find-goal-relevant-concept-seeds remaining-goals)
	       collect (create-opmatch concept problem)))
    (if dgs-debug* (format t "~&goal-relevant concept selection seeds: ~A" goal-relevant-concept-seeds))

    ;; generate maximal matches through iterative sampling search
    (setq maximal-candidates
	  (loop for candidate in (append goal-relevant-skill-seeds goal-relevant-concept-seeds)
	     append
    
	       (terminal-nodes
		(iterative-sampling-search candidate #'next-opmatch
					   :depth-limit (+ 1 
							   (length (opmatch-preconditions-to-go candidate)) 
							   (length (opmatch-postconditions-to-go candidate)))))))

    ;; filter out duplicate candidates
    (setf maximal-candidates (remove-duplicates maximal-candidates :test #'same-opmatch))

    ;; apply filters
    (setq maximial-candidates
	  (loop for m in maximal-candidates
	       unless (or (has-ill-formed-bindings m)
			  (and bind-unchainables? (satisfies-unchainable-conditions m))
			  (match-failed-operator problem (opmatch-operator m) (opmatch-bindings m))
			  )
	       collect m))

    (if debug* (format t "~&maximal goal-relevant candidates : ~A" maximal-candidates))

    (when dgs-debug* 
	(format t "~&Final candidate set before selection heuristic: ~&~A ~&" maximal-candidates)
	(setq final-candidates* maximal-candidates))

    ;; apply the operator selection heuristic
    (setq selected-candidate
	  (operator-selection-heuristic (append maximal-candidates actionable-seeds)))

    ;; return the winning operatorr
    selected-candidate))



(defun satisfies-unchainable-conditions (candidate)
 ;; CHECK to see if this makes any sense if the candidate reflects a concept vs a skill ***
  (let* ((operator (opmatch-operator candidate))
	 (bindings (opmatch-bindings candidate))
	 ;; grab all conditions for the unchainable test
	 (conditions (append (opmatch-preconditions-unmatched candidate) (opmatch-preconditions-matched candidate)))
	 (unchainable-conditions (get-unchainable-relations conditions)))
    (find-all-match-bindings-for-literals unchainable-conditions bindings cstm*)))


(defun has-ill-formed-bindings (candidate)
  (ill-formed-binding-list (opmatch-bindings candidate)))

(defun find-goal-irrelevant-actionable-skills (goals)
  ;; returns an opmatch whose bindings make all conditions of the skill true
  ;; provided the skill's effects are irrelevant to goals
  (loop for item in (find-actionable-skills goals)
       unless (skill-relevant-to-goals (opmatch-operator item) (opmatch-bindings item) goals)
       collect item))

(defun find-actionable-skills (goals)
  ;;returns a list of skillmatches that make all conditions of the skill true
  ;;absent any prior bindings
  (loop for skill in sltm* append (actionable-skill skill goals)))

(defun actionable-skill (skill goals &optional prior-bindings &aux res)
  ;; returns a list of skillmatches that make all conditions for this skill true
  ;; or nil if there are none

  ;;CHECK TO  MAKE SURE THIS FUNCTION RETURNS COMPLETE MATCHES OR NIL*****

  (loop for bindings in
       (find-all-match-bindings-for-literals (sclause-conditions skill) prior-bindings cstm*)
     collect (make-opmatch
	      :operator skill
	      :preconditions-matched (sclause-conditions skill)
	      :bindings (append prior-bindings bindings)
	      :goals-unmatched goals)))

(defun skills-relevant-to-goals (goals)
  ;; returns a list of skills that have some effect that unifies with any goal in goals
  (loop for skill in sltm*
       when (skill-relevant-to-goals skill nil goals) 
       collect skill))

(defun skill-relevant-to-goals (skill prior-bindings goals &aux res)
    ;; returns true if this skill has an effect that unifies with any goal in goals, given the prior bindings
  (loop named outer-loop
     for effect in (csubst-bindings prior-bindings (sclause-effects skill)) do
       (loop for goal in goals do
	    (setq res  (unify-match goal effect))
	    (if res (return-from outer-loop t)))))

(defun find-goal-relevant-concept-seeds (goals &optional (concepts cltm*))
  ;; find non-primitive concepts that pertain to any goal in goals
  ;; Do not save any bindings.
  (loop for concept in concepts 
     when (and (concept-relations concept) (concept-relates-to-goals concept goals))
     collect concept))

(defun concept-relates-to-goals (concept goals)
  ;; concepts match onto the positive part of goals
  (let ((target nil))
    (loop for goal in goals do
	 (if (negative-clause goal)
	     (setq target (second goal))
	     (setq target goal))
       when (unify (concept-head concept) target) return concept)))

;; believe this code no longer accessible
(defun unsatisfied-goals-for-problem (problem)
  ;; finds all unsatisfied goals for problem, including goals brought in by constraints, and eliminating goals ruled out by constraints
  ;; returns literals with variables instantiated
  (let ((goals-added nil)
	(unsatisfied-goals nil)
	(goals-to-delete nil))

    ;; Step 1: Get all the goals in the current problem that are unsatisfied and that
    ;; have not failed before.
    ;; dgs: goals no longer fail so eliminate test
    (loop for goal in (csubst-bindings (problem-bindings problem) 
				      (problem-objectives problem))
	 when (not (goal-literal-satisfied? goal))

;; focal goals no longer exist, so only problems, intentions and their bindings can fail
;;	  when (and (not (goal-literal-satisfied? goal))
;;	            (not (member-failure-context-list? :problem-bindings (problem-bindings problem))))
						  
	  do
	  (push goal unsatisfied-goals))

    ;; Step 2: Get all the goals added by add constraints and all the goals
    ;; deleted by ordering constraints.
    (loop for constraint in constraint-memory*
	  when (constraint-active? constraint unsatisfied-goals)
	  do
	  (cond ((constraints-add constraint)
		 (setq goals-added (append (csubst-bindings (constraints-bindings constraint)
							   (constraints-add constraint))
					   goals-added))
		 (print "Found an active add constraint."))
		((constraints-delete constraint)
		 (setq goals-to-delete (append (csubst-bindings (constraints-bindings constraint)
							       (constraints-delete constraint))
					       goals-to-delete))
		 (print "Found an active delete constraint."))))
    
    ;; Step 3: Remove all goals marked for deletion.
    (loop for goal in goals-to-delete
	  do
	 (setf goals-added (delete goal goals-added :test #'equal))
	 (setf unsatisfied-goals (delete goal unsatisfied-goals :test #'equal)))

    (if debug* (format t "~&Return from collect-goals-relevant-to-skills: ~&  Added goals ~A ~& Unsatisfied goals: ~A" goals-added unsatisfied-goals))
    (append goals-added unsatisfied-goals)))


(defun find-all-candidates-satisfying-unchainable-conditions (sclause bindings)
  (let* ((unchainable-conditions (get-unchainable-relations (sclause-conditions sclause)))
	 (good-bindings (find-all-match-bindings-for-literals unchainable-conditions
							      bindings
							      cstm*)))
    (loop for good-binding in good-bindings
	 collect (list sclause good-binding bindings))))

(defun max-effects-matched-heuristic (pair problem)
  (let* ((goal-literals (problem-objectives problem))
	 (unsatisfied-goal-literals nil)
	 (skill (car pair))
	 (bindings (second pair))
	 (target-literals (csubst-bindings bindings
					  (sclause-effects skill)))
	 (result nil))

    (loop for goal in (csubst-bindings (problem-bindings problem)
				      goal-literals)
	  when (not (goal-literal-satisfied? goal))
	  do
	  (push goal unsatisfied-goal-literals))

    ;; result is  NIL or (bindings matches-1 matches-2)
    (setq result
	  (repeat-greedy-partial-unify-with-targets unsatisfied-goal-literals 
						    target-literals))
    (if result
	(length (second result))
	0)))

(defun min-unsatisfied-conditions-heuristic (pair)
  (let ((skill (car pair))
	(bindings (second pair)))
    (find-number-of-unsatisfied-conditions skill bindings)))

(defun find-number-of-unsatisfied-conditions (skill bindings)
  (let ((max-match-list nil)
	(max-match nil))

    (setq max-match-list
	  (find-all-max-size-partial-matches-for-literals (sclause-conditions skill) bindings cstm*))
    
    ;; NOTE: This is a possible backtrack point but specific to the min-unsatisfied-conditions heuristic.
    (setq max-match (random-choose max-match-list))

    (- (length (sclause-conditions skill))
       (length (car max-match)))))

(defun find-matching-concept (focus &key problem-bindings ignore-failure-context?)
  (let* ((negated-focus? (eq (car focus) 'not))
	 (to-match (cond (negated-focus?
			  (cadr focus))
			 (t
			  focus))))
    
    (loop with result = nil
	  for concept in cltm*
	  ;; Note: Here the order of arguments to unify-match matters.
	  for (flag . bindings) = (unify-match to-match
					       (concept-head concept))
	  while (not result)
	  when
	 (and flag
	      (or ignore-failure-context?
		  (error "find-matching-concept asking if concept member of failure-context-list")

;; THIS CODE CANNOT BE ACCESSED SINCE ROUTINE ONLY CALLED WITH IGNORE-FAILURE-CONTEXT = t
;;		  (not (concept-member-of-failure-context-list? 
;;			problem-bindings 
;;			focus
;;			(if negated-focus?
;;			    (car (get-chainable-negations
;;				  (csubst-bindings bindings
;;						  (concept-relations concept))))
;;			    (concept-relations concept))))

		  ))
	  do
	  (push (list focus
		      (concept-relations concept)
		      bindings)
		result)
	  finally
	  (when result
	    (return (random-choose result))))))



(defun repeated-problem? (problem)
  (let ((pstack (get-problem-stack-above problem)))
    (loop for p in pstack
	 thereis (problem-is-subset problem p))))


	 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Structures and functions for constraints
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;type can be BINDINGS-CONSTRAINT or GOAL-CONSTRAINT
(defstruct constraints
  name
  id
  type
  goal-conditions
  belief-conditions
  add
  delete
  bindings
)

(defmacro create-constraints (&rest constraints)
  `(let ((constraints (quote ,constraints))
	 result)
     (do ((next-constraint (car constraints) (car constraints)))
	 ((null constraints)
	  (setq constraint-memory* (append constraint-memory* (reverse result))) nil)
       (push (create-constraint-clause next-constraint) result)
       (pop constraints))))

(defun create-constraint-clause (constraint)
  (let ((name (car constraint))
	(id nil)
	(type nil)
	(goal-conditions nil)
	(belief-conditions nil)
	(add nil)
	(delete nil))
    
    (pop constraint)				; get rid of name, rest is alternating :key <spec> pairs
    (do ((next-field (car constraint) (car constraint))
	 (next-spec (cadr constraint) (cadr constraint)))
	((null constraint)
	 (cond ((null id) (setq id (incf id-count*))))
	 (make-constraints :name name
		       :id id
		       :type type
		       :goal-conditions goal-conditions
		       :belief-conditions belief-conditions
		       :add add
		       :delete delete))

      (cond ((eq next-field ':id)(setq id next-spec))
	    ((eq next-field ':type)(setq type next-spec))
	    ((eq next-field ':goal-conditions)(setq goal-conditions next-spec))
	    ((eq next-field ':belief-conditions)(setq belief-conditions next-spec))
	    ((eq next-field ':add)(setq add next-spec))
	    ((eq next-field ':delete)(setq delete next-spec))
	    (t (print-error next-field "field" "constraint")))
      (setq constraint (cddr constraint)))))

;; Check if a constraint is active.
(defun constraint-active? (constraint goal-list)
  (let ((constraint-matched? nil)
	(g-list (copy-list goal-list)))

    (when (eq (constraints-type constraint)
	      'GOAL-CONSTRAINT)
      ;; Match goal-conditions
      (loop with i = 1
	    with result = nil
	    with tliteral = nil
	    while (and (<= i (length g-list))
		       (not constraint-matched?))
	    do
	    ;; result is of the form (matched-literals bindings)
	    (setq result (pattern-match-literals (constraints-goal-conditions constraint)
						 g-list
						 t))
	    (cond ((eq (length (constraints-goal-conditions constraint))
		       (length (car result)))
		   (setq constraint-matched? t)
		   (setf (constraints-bindings constraint)
			 (second result)))
		  ;; shuffle the goal-list to generate a different permutations of literals
		  (t
		   (incf i)
		   (setq tliteral (pop g-list))
		   (setq g-list (append g-list (list tliteral))))))

      ;; Match belief-conditions
      (when (and constraint-matched?
		 (constraints-belief-conditions constraint))
	(setq constraint-matched?
	      (exists-match-bindings-for-literals? (constraints-belief-conditions constraint)
						   (constraints-bindings constraint)
						   cstm*))))
    constraint-matched?))

(defun violates-binding-constraints? (g-list)
  (let ((constraint-matched? nil))
    
    (loop for constraint in constraint-memory*
	  while (not constraint-matched?)
	  when (eq (constraints-type constraint)
		   'BINDINGS-CONSTRAINT)
	  do
	  
	  ;; Match goal-conditions
	  (loop with i = 1
		with result = nil
		with tliteral = nil
		while (and (<= i (length g-list))
			   (not constraint-matched?))
		do
		;; result is of the form (matched-literals bindings)
		(setq result (pattern-match-literals (constraints-goal-conditions constraint)
							    g-list
							    t))
		(cond ((eq (length (constraints-goal-conditions constraint))
			   (length (car result)))
		       (setq constraint-matched? t)
		       (setf (constraints-bindings constraint)
			     (second result)))
		      ;; shuffle the goal-list to generate a different permutations of literals
		      (t
		       (incf i)
		       (setq tliteral (pop g-list))
		       (setq g-list (append g-list (list tliteral))))))
	  
	  (when constraint-matched?
	    (setq constraint-matched? (exists-match-bindings-for-literals? (constraints-belief-conditions constraint) 
										(constraints-bindings constraint) 
										cstm*))))
    ;;(if constraint-matched?
	;;(print "Found a violated bindings-constraint. Rejecting the current bindings."))
    
    constraint-matched?))
    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Set Up Correspondence of Goal-Targets and Targets
;;;    (and update bindings of intention based on match)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; assumes problem already has an intention
(defun establish-correspondence-for-intention-targets (problem)
  (let* ((intention (problem-intention problem))
	 (intention-bindings (intention-bindings intention))
	 (target-literals (csubst-bindings intention-bindings
					  (intention-effects intention)))
	 (problem-bindings (problem-bindings problem))
	 (goal-literals (remove-satisfied-literals
			 (csubst-bindings problem-bindings
					 (problem-objectives problem)))))

    (multiple-value-bind (gensymized-goal-literals gensym-bindings)
	(gensymize-vars goal-literals)
      
      (let* ((correspondence-match ; ( norvig-bindings matched-goals matched-targets)
	      (greedy-partial-unify-with-targets gensymized-goal-literals 
						 target-literals))
	     (correspondence-bindings (first correspondence-match))
	     (all-target-goal-literals ; undo gensymizing of goal-literals
	      (de-gensymize-vars (second correspondence-match)
				 gensym-bindings))
	     (all-target-literals (third correspondence-match))
	     (unification-bindings-for-all-target-literals
	      (unify all-target-literals
		     (norvig-subst-bindings correspondence-bindings
					    all-target-goal-literals)))
	     (icarus-bindings-form-for-targets
	      (convert-norvig-bindings-to-icarus
	       unification-bindings-for-all-target-literals))
	     (icarus-bindings-for-targets
	      (rest icarus-bindings-form-for-targets)))
	;; check whether anything failed (that shouldn't happen)
	;;  Check that all-target-goal-literals and all-target-literals
	;;     are non-null and of same length
	(if (and all-target-goal-literals
		 all-target-literals
		 (not (= (length all-target-goal-literals)
			 (length all-target-literals))))
	    (warn "~%Bad Correspondence-lists:~%   ~a~%   ~a"
		  all-target-goal-literals
		  all-target-literals))
	
	(if (and all-target-goal-literals
		 all-target-literals)
	    
	    ;; set problem-target-goals
	    (setf (problem-target-goals problem)
		  all-target-goal-literals)
	       
	    ;; set intention-bindings -- making sure that the problem-bindings are properly
	    ;; inherited as the intention-bindings
	    (setf (intention-bindings intention)
		  (append icarus-bindings-for-targets
			  intention-bindings))
	    
	    ;; set intention-targets
	    (setf (intention-targets intention)
		  (csubst-bindings icarus-bindings-for-targets
				  all-target-literals)))))))

(defun remove-satisfied-literals (literal-list)
  (loop for literal in literal-list
	unless
	(goal-literal-satisfied? literal)
	collect literal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Functions to generate list of unchainable conditions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun extract-unchainable-conditions(cltm sltm)
  (let ((neg-hierarchical-concepts nil)
	(pos-chainables nil)
	(neg-chainables nil))
    
    ;; Consider all primitive concepts and their negations as possibly unchainable
    ;; Also create a list of negations of hierarchichal concepts.
    (loop with ccopy = nil
	  for concept in cltm
	  do
	  (cond ((null (concept-relations concept))

		 (when (not (member (car (concept-head concept)) 
				    pos-unchainable-conditions* :test #'equal))
		   (push (car (concept-head concept)) 
			 pos-unchainable-conditions*))

		 (when (not (member (car (concept-head concept)) 
				    neg-unchainable-conditions* :test #'equal))
		   (push (car (concept-head concept)) 
			 neg-unchainable-conditions*))

		 (setq cltm
		       (remove concept cltm :test #'equal)))

		(t
		 (setq ccopy (copy-concept concept))
		 (setf (concept-head ccopy)
		       (list 'not (concept-head ccopy)))
		 (push ccopy neg-hierarchical-concepts))))
    
    ;; All concepts that are achieved by a skill are chainable.
    ;; Remove them from the lists (pos-unchainable-conditions*, neg-unchainable-conditions*, cltm,
    ;; neg-hierarchical-concepts), if present.
    (loop for skill in sltm
	  do
	  (loop for effect in (sclause-effects skill)
		do
		(cond ((not (eq (car effect) 'not))
		       (when (not (member (car effect) 
					  pos-chainables :test #'equal))
			 (push (car effect) pos-chainables))
		       (setq pos-unchainable-conditions*
			     (remove (car effect) pos-unchainable-conditions* :test #'equal))
		       (setq cltm
			     (remove (car effect) cltm :test #'(lambda (literal concept)
								 (eq literal (car (concept-head concept)))))))
		      (t
		       (when (not (member (caadr effect) 
					  neg-chainables :test #'equal))
			 (push (caadr effect) neg-chainables))
		       (setq neg-unchainable-conditions*
			     (remove (caadr effect) neg-unchainable-conditions* :test #'equal))
		       (setq neg-hierarchical-concepts (remove (caadr effect) neg-hierarchical-concepts
							       :test #'(lambda (literal concept)
									 (eq literal (caadr (concept-head concept))))))))))

    ;; Loop through remaining hierarchical concepts,
    ;; and determine if they are unchainable. This 
    ;; process is recursive.
    (loop for concept in cltm
	  do
	  (when (and (all-relations-unchainable (concept-relations concept) pos-chainables neg-chainables)
		     (not (member (car (concept-head concept)) 
				    pos-unchainable-conditions* :test #'equal)))
	    (push (car (concept-head concept)) 
		  pos-unchainable-conditions*)))

    ;; Loop through remaining negations of hierarchical concepts,
    ;; and determine if they are unchainable. This 
    ;; process is recursive.
    (loop for concept in neg-hierarchical-concepts
	  do
	  (when (and (all-relations-unchainable (concept-relations concept) pos-chainables neg-chainables)
		     (not (member (caadr (concept-head concept)) 
				    neg-unchainable-conditions* :test #'equal)))
	    (push (caadr (concept-head concept)) 
		  neg-unchainable-conditions*)))))

(defun all-relations-unchainable(relations pos-chainables neg-chainables)
  (loop for relation in relations
	always (is-unchainable relation pos-chainables neg-chainables)))

(defun is-unchainable(relation pos-chainables neg-chainables)
  (let ((concept-triplet (find-matching-concept relation
						:problem-bindings nil
						:ignore-failure-context? t)))
    (cond 
      ;;positive concept
      ((not (eq (car relation) 'not))
       (cond ((member (car relation)
		      pos-unchainable-conditions*
		      :test #'equal)
	      t)
	     ((member (car relation)
		      pos-chainables
		      :test #'equal)
	      ;;Chainable concept
	      nil)
	     (t
	      (all-relations-unchainable (second concept-triplet) 
					 pos-chainables neg-chainables))))
      
      ;;negated-concept
      (t
       (cond ((member (caadr relation)
		      neg-unchainable-conditions*
		      :test #'equal)
	      t)
	     ((member (caadr relation)
		      neg-chainables
		      :test #'equal)
	      ;;Chainable concept
	      nil)
	     (t
	      (all-relations-unchainable (negate-relations 
					  (second concept-triplet))
					 pos-chainables neg-chainables)))))))

(defun negate-relations(relations)
  (let ((negated-relations nil))
    (loop for relation in relations
	  do
	  (cond ((eq (car relation) 'not)
		 (push (cadr relation) negated-relations))
		(t
		 (push (list 'not relation) negated-relations))))
    negated-relations))

(defun get-chainable-negations(relations)
  (let ((bindings nil))
    
    (setq bindings (find-all-match-bindings-for-literals relations nil cstm*))
    (if bindings
	(setq bindings (random-choose bindings)))
    
    (mapcar #'(lambda (relation)
		(setq relations (remove relation relations :test #'equal)))
	    (get-unchainable-relations relations))
    
    (list (negate-relations relations)
	  bindings)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Using unchainable relations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; First idea:
;;  Use in skill-selection to make sure all candidate skills 
;;    have all unchainable conditions satisfied

(defun unchainable? (relation)
  (cond ((eql (car relation) 'not)
	 (member (car (second relation))
		 neg-unchainable-conditions*))
	(t
	 (member (car relation)
		 pos-unchainable-conditions*))))

(defun get-unchainable-relations (relation-list)
  (loop for relation in relation-list
       when (unchainable? relation)
       collect relation))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Code to detect execution loops
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defparameter execution-loop* nil)

(defun get-current-state (cstm)
  (mapcar #'cinstance-head cstm))

(defun store-intention (intention)
  (if gstm*
      (push (intention-head intention)
	    (problem-repeating-intentions (car gstm*)))))

(defun get-repeating-intentions ()
  (problem-repeating-intentions (car gstm*)))

;;Stores a state with probability P. Presently P = 1/3.
(defun store-state (state)
  (when (and gstm*
	     (= (random 3)
		(random 3)))
    (push state (problem-visited-states
		 (car gstm*)))
    (print "Stored current belief state.")))

(defun repeated-state? (state)
  (let ((visited-states (if gstm* 
			    (problem-visited-states 
			     (car gstm*))))
	(repeated? nil))

    (loop with matched-literals=nil
	  for visited-state in visited-states
	  while (not repeated?)
	  do
	  (setq matched-literals (pattern-match-literals state visited-state))
	  (if (eq (length matched-literals)
		  (length visited-state))
	      (setq repeated? t)))
    repeated?))

(defun reset-loop-traces ()
  (setq execution-loop* nil)
   (setf (problem-repeating-intentions (car gstm*)) nil)
   (setf (problem-visited-states (car gstm*)) nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; User interface functions (descended from compiler.lisp &
;;; interpreter.lisp)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This function takes problem-forms -- a list of goal literals,
;; creates a list of problems from it and assigns the list to 
;; gstm*.
(defmacro create-problems (&rest problem-forms)
  `(setf gstm* 
    (loop for form in (quote ,problem-forms)
     collect 
     (make-problem-from-clauses form :gensymize nil))))

(defun replace-problem (old new)
  ;; replace problem in gstm*
  (setf gstm* (remove old gstm*))
  (push new gstm*)
  new)

(defun pprob () (print-problems))

(defun print-problems ()
  (cond ((null gstm*)
	 (terpri) (princ "No problems are specified."))
	(t
	 (terpri) (princ "Top level problems")
	 (mapcar #'pprint-problem-objectives gstm*))))

(defun print-skills ()
  (terpri)(princ "Skills:")(terpri)
  (mapc #'(lambda (c) (print-clause c)(terpri)) sltm*) 
  nil)

(defun ps () (print-skills))

(defun print-clause (clause)
  (terpri)(princ "(")(princ (sclause-head clause))
  (princ "  :id ")(princ (sclause-id clause))
  (cond ((not (null (sclause-elements clause)))
	 (terpri)(princ " :elements ")(princ (sclause-elements clause))))
  (cond ((not (null (sclause-conditions clause)))
	 (terpri)(princ " :conditions    ")(princ (sclause-conditions clause))))

  (cond ((not (null (sclause-subskills clause)))
	 (terpri)(princ " :subskills ")(princ (sclause-subskills clause))))
  (cond ((not (null (sclause-actions clause)))
	 (terpri)(princ " :actions  ")(princ (sclause-actions clause))))
  (cond ((not (null (sclause-effects clause)))
	 (terpri)(princ " :effects  ")(princ (sclause-effects clause))))
  (princ ")"))

(defun display-active-problem-stack ()
  (cond ((null active-problem*)
	 (format t "~%No Active Problem"))
	(t
	 (loop for problem = active-problem* then (intention-problem-parent intent)
	    for intent = (problem-i-parent problem)
	    while intent
	    do
	      (pprint-problem problem)
	      (pprint-intention intent)
	    finally
	      (pprint-problem problem)))))

(defun set-skill-selection-heuristic () (change-skill-selection-heuristic))	      
(defun change-skill-selection-heuristic()
  (let ((heuristic-list (list 'MAXIMUM-EFFECTS-MATCHED
			      'MINIMUM-UNSATISFIED-CONDITIONS)))

    ;; Print the available options
    (format t "~%~%*********************************")
    (format t "~%Here are the available heuristics:")
    (loop for i from 1
	  for heuristic in heuristic-list
	  do
	  (format t "~%   ~a  ~a" i heuristic))

    ;; Prompt user and read selection
    (format t "~%Enter the number of the heuristic you want to select :")
    (let ((choice (read)))
      (cond ((and (numberp choice)
		  (> choice 0)
		  (<= choice (length heuristic-list)))
	     (cond ((= choice 1)
		    (setq skill-selection-heuristic* :MAX-EFFECTS-MATCHED)
		    (format t "~%Skill selection heuristic set to Maximum Effects Matched."))
		   ((= choice 2)
		    (setq skill-selection-heuristic* :MIN-UNSATISFIED-CONDITIONS)
		    (format t "~%Skill selection heuristic set to Minimum Unsatisfied Conditions."))))
	    (t
	     (format t "~%~%INVALID CHOICE! TRY AGAIN."))))))

(defun set-search-direction()
  (let ((options (list 'BACKWARD
		       'FORWARD)))

    ;; Print the available options
    (format t "~%~%*********************************")
    (format t "~%Here are the available choices:")
    (loop for i from 1
	  for option in options
	  do
	  (format t "~%   ~a  ~a" i option))

    ;; Prompt user and read selection
    (format t "~%Enter your choice :")
    (let ((choice (read)))
      (cond ((and (numberp choice)
		  (> choice 0)
		  (<= choice (length options)))
	     (cond ((= choice 1)
		    (setq search-direction* :BACKWARD)
		    (setq skill-selection-heuristic* :MAX-EFFECTS-MATCHED)
		    (format t "~%Search direction set to backward."))
		   ((= choice 2)
		    (setq search-direction* :FORWARD)
		    (setq skill-selection-heuristic* :MIN-UNSATISFIED-CONDITIONS)
		    (format t "~%Search direction set to forward."))))
	    (t
	     (format t "~%~%INVALID CHOICE! TRY AGAIN."))))))

(defun clear+ ()
  (clear-concepts)                      ; cltm*
  (if (equal inference* 'fast) (clear-fast-matcher))
  (clear-skills)                        ; sltm*
  (clear-goals)                         ; gstm*
  (setq id-count* 0)
  ;; additional clearings
  (setf concepts* nil)
  (setf primitive-concepts* nil)
  (setf pstm* nil)
  (setf cstm* nil)
  (setf cycle* nil)

  (setf cycle* 0)
  (setf gtrace* t)			; goal print
  (setf ptrace* 1) ; 1 for organized print, and 2 for raw print of percepts
  (setf btrace* t)			; belief print
  (setf ctrace* t)			; cycle print
  (setf atrace* t)			; action print
  (setf etrace* t)			;
  (setf debug* nil)

  (setf halt* nil)
  (setf failed* nil)
  (setf inference* 'FAST)
  ;; are these necessary?
  (setf starttime* nil)
  (setf astm* nil)

  ;; globals from solver-rewrite
  (setf active-problem* nil)
  (setf executing-intention* nil)
  (setf constraint-memory* nil
	pos-unchainable-conditions* nil
	neg-unchainable-conditions* nil)

  t)




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; User interface functions for execution traces
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Utility function
(defun exec-trace (&optional enable-problem-solving?)
  (setf pat-trace* t
	problem-solver-enabled* enable-problem-solving?
	*print-right-margin* 78))

(defmacro execute-skill (skill-form)
  `(progn (exec-trace)  ; execution-only, this turns off problem-solving
	  (run 1)
	  (execute-skill+  ,skill-form)))

(defmacro execute-skill+ (skill-form)
  `(progn (exec-trace)
	  (cond ((call-intention (quote ,skill-form))
		 (loop while executing-intention*
		    do
		      (cont 1))
		 (format t "~%~%Execution stopped because Executing Intention is NIL~%"))
		(t (format t "~%~% Call to skill-form FAILED: ~a~%"
			   (quote ,skill-form))))))

;;;;;;;;;;;;UNUSED
(defun collect-skills-relevant-to-goals (goals &aux res)
;; finds skills relevant to goals, with skills and goals taken in
;; isolation.  Each match is essentially a seed for further matches.

  (loop for skill in sltm*
	  do
	  (loop for effect in (sclause-effects skill)
	     do
	       (loop for goal in goals
		  for (flag . bindings ) = (unify-match goal effect)
		  do
		    (when flag
		      (push (list effect skill bindings) res)))))
  (if debug* (format t "~&Results from collect-skills-relevant-to-goals ~A" res))
  res)

