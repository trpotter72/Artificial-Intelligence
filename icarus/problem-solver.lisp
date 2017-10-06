;; problem solver functions
;;  - dgs 03/2012

;; repackaging and partial rewrite of core problem solver functions to rely on iterative sampling
;; when selecting bindings and operators (and soon, problem decompositions)

(defvar debug-select-bindings* t)

;;;; macros
(defmacro transfer-bindings (vars from-place var-map to-place)
  `(append-to-place (map-all-bindings ,vars from-place var-map to-place) to-place))

(defmacro transfer-bindings2 (vars from-place var-map to-place)
  (let ((item (gensym)))
    `(let ((,item (map-all-bindings ,vars ,from-place ,var-map ,to-place)))
       (append-to-place ,item ,to-place))))
;;;;;;


(defun select-bindings (problem)
;; This function advances the problem by selecting bindings, or backtracking if no suitable
;; extension can be found.  It operates by side-effect on the problem tree and problem structure.

;; Tests problem objectives against beliefs via iterative sampling. Prefers full to partial matches.

  (let* ((seed (make-opmatch :problem problem
			     :preconditions-to-go (problem-objectives problem)
			     :bindings (problem-bindings problem)))
	 (results (iterative-sampling-search 
		   seed #'next-opmatch
		   :successp #'full-precondition-match
		   :failurep #'unmatched-unchainable-precondition
;;		   :failurep #'no-precondition-match
		   :depth-limit (1+ (length (opmatch-preconditions-to-go seed)))))
	 (full-matches (remove-duplicates (successfull-nodes results) :test #'same-opmatch))
	 (partial-matches  (remove-duplicates (terminal-nodes results) :test #'same-opmatch)))

    (if debug-select-bindings* (setq iss-bindings* results))

  (cond 
    ;; problem completely solved by the bindings found, no form of failure possible
    (full-matches
     (capture-bindings (random-choose full-matches) problem)

     ;; done with this problem, communicate bindings found to parent intention
     (transfer-bindings-to-parent problem) 
     (report-problem-solved problem)
     (react-to-full-match problem))

    ;; useable partial-matches
    ((setq partial-matches
	   (remove-if-any partial-matches #'known-bad-bindings))
     (capture-bindings (random-choose partial-matches) problem)
     (react-to-partial-match problem))
	
    ;; no way forward, so fail problem with its original bindings and backtrack
    (t 
     (fail-problem-bindings problem)
     (backtrack)))))

(defun react-to-full-match (problem &aux (results (problem-bindings problem)) parent-intention parent-problem)
  ;; All of the input problem's clauses match against beliefs. 

  ;; Access the parent intention, and parent problem.  If this problem repeats the parent problem,
  ;; fail it. If solving this problem means the parent intention is executable, execute it if its
  ;; consequences are acceptible.  If this problem was the result of concept chaining, capture the
  ;; bindings in the parent problem and continue problem solving.

  (setq parent-intention (problem-i-parent problem))
  (setq parent-problem (if parent-intention (intention-problem-parent parent-intention)))

  (cond ((null parent-intention)
	 (report-toplevel-problem-satisfied)
	 (setq active-problem* nil))

	;; the parent intention with these bindings has failed before *** Check correct use of parent-problem
	((match-failed-intention parent-problem parent-intention)
	 (fail-intention parent-intention)
	 (backtrack))

	;; problem represented a satisfied chained concept
	((null (intention-id parent-intention))
	 ;; Bug?? Shouldn't this capture bindings in parent problem? Fix ***
	 (print "All conditions of the chained-concept satisfied, selecting new bindings for parent problem.")
	 (setq active-problem* parent-problem)
	 (setf (problem-bindings-selected? active-problem*) nil))

	((repeating-intention parent-intention)
	 (format t "~&Intention ~A is a repeating intention" (intention-head (problem-i-parent problem)))
	 (reset-loop-traces)
	 (fail-intention parent-intention)
	 (backtrack))

	;; executable intention
	((monotonic-progress parent-intention parent-problem)
	 ;; WARNING: this test significantly alters belief memory for the rest of this cycle
	 ;; Check intention's consequences based on deductive closure over effects.
	 ;; Demand monotonic progress on problems above this point in the problem tree.
	 ;; DGS 6/5/2011

	 (format t "~&Consequences of intention ~A are acceptable, moving to execution"
		(csubst-bindings (intention-bindings parent-intention) (intention-head parent-intention)))
	 (set-executing-intention parent-intention)
	 (setq active-problem* parent-problem)
	 (setf (problem-bindings-selected? active-problem*) nil))
	
	;; non-executable intention
	(t
	 (format t "~&Consequences unacceptable, failing intention ~A with bindings ~A and backtracking"
		 (intention-head parent-intention)
		 (intention-bindings parent-intention))
	 (fail-intention parent-intention)
	 (backtrack))))


(defun react-to-partial-match (problem)
  ;; rejects the bindings (without backtracking), or accepts them if they pass inspection

  (let* ((bindings (problem-bindings problem))
	 (objectives (problem-objectives problem))
	 (instantiated-objectives (csubst-bindings bindings objectives)))
    (cond 
      ((repeated-problem? problem)
       (print "Found a repeated problem! Reporting the current bindings as a failure.")
       (setf (problem-bindings-selected? problem) nil) ; give up on these bindings
       (create-and-store-failure-context problem :problem-bindings bindings))

      ((flipped-problem-objectives? problem)
       (format t "~&Problem ~A negates a problem further up the stack" instantiated-objectives)
       (setf (problem-bindings-selected? problem) nil) ; give up on these bindings
       (create-and-store-failure-context problem :problem-bindings bindings))

      (t
       ;; This problem is worth pursuing.
       (setf (problem-intention problem) nil) ;; hygiene, to make sure a new intention is chosen
       ;;     (setf (problem-focus problem) nil) ; should be unused, can eliminate

       (format t "~% Partial match leaves these Unsatisfied goals: (")
       (loop for goal in instantiated-objectives
	  when (not (goal-literal-satisfied? goal))
	  do
	  (format t "~a" goal))
       (format t ")~%"))

      ;; This problem and its bindings duplicate those in some parent up the stack.
      ;; Keep pursuing this problem, but mark these bindings as a failure. 
      )))

(defun repeating-intention (intention)
  (and execution-loop*
       (member (intention-head intention) (get-repeating-intentions) :test #'equal)))


(defun unmatched-unchainable-precondition (opm)
  ;; returns true if this opmatch has no further preconditions to chew on, and at least one
  ;; unchainable condition is unmatched
    (if (null (opmatch-preconditions-to-go opm))
	(loop for precond in (opmatch-preconditions-unmatched opm)
	     when (unchainable? precond) return t)))


(defun full-precondition-match (opm)
 ;; returns true if this opmatch represents a complete match to a problem
  (if (null (opmatch-preconditions-to-go opm))
      (or 
       ;; satisfied at least one disjunctive goal
       (and (problem-disjunctive-goal-list? (opmatch-problem opm))
	    (>= (length (opmatch-preconditions-matched opm) 1)))
       
       ;; all preconditions addressed and all were matched
       (null (opmatch-preconditions-unmatched opm)))))



(defun no-precondition-match (opm)
  ;; returns true if this opmatch made no progress
  (if (null (opmatch-preconditions-to-go opm))
      (null (opmatch-preconditions-matched opm))))


(defun remove-if-any (oblist &rest filter-fns &aux (res oblist))
  (loop for fn in filter-fns do
       (setq res (remove-if fn res)))
  res)

(defun unchainable-conditions-remain (opm) (not (satisfies-unchainable-conditions opm)))

(defun known-bad-bindings (opm)  
 ;; FIX opmatch to know the motivating problem, extract and pass it to member-failure-context-list
 ;; instead of relying on bank shot through global variable
  (match-failed-bindings  (opmatch-problem opm)  (opmatch-bindings opm)))

(defun backtrack (&optional (from-problem active-problem*))
  ;; Unwinds the problem tree by setting the active problem to the parent of the current problem.
  ;; This blows off the intention that spawned  active-problem* as well.
  (cond ((problem-i-parent from-problem)
	 (format t "~&Backtracking from problem ~A" (problem-objectives from-problem))
	 (setq active-problem* (intention-problem-parent (problem-i-parent from-problem)))

	 ;; too aggressive - keep the bindings of the problem this backtracks into
;;	 (setf (problem-bindings active-problem*) nil) 
;;	 (setf (problem-bindings-selected? active-problem*) nil)
	 (setf (problem-intention active-problem*) nil)
	 (incf nodes-failed*))
	(t 
	 ;; no parent so failing top level problem
	 (format t "~2&****Backtracking out of top-level problem")
	 (setq active-problem* nil))))





;;;;;;;;;;;;;;;;;;;; 
;; binding maps
;; tools for mapping variables across naming spaces, and communicating values across naming spaces

(defun map-all-bindings (vars from-env var-map to-env)
  (loop for v in vars when (map-binding v from-env var-map to-env) collect it))

(defun map-binding (var from-env var-map to-env)
   ;; returns nil, or a binding pair that links the variable corresponding to var in to-env with the
   ;; value of var in from-env
  ;; ASSUMES that var is linked in some way across both environments (BAD ASSUMPTION!!)

  (let* ((binding (get-chained-binding var from-env))
	 (binding-map (binding-map-lookup var var-map))
	 (to-var (if binding-map (cdr binding-map))))

    (when (and binding to-var)  ;; var had a value and a mapping into to-env
      (unless (get-chained-binding to-var to-env)  ; return nil if var was already bound in to-env
	(cons to-var (cdr binding))))))

(defun binding-map-lookup (var var-map)
  ;;treat the var-map as a bi-directional structure
  (or (assoc var var-map) (reverse-binding (rassoc var var-map))))

(defun reverse-binding (binding) (if (consp binding) (cons (cdr binding) (car binding))))

;;;;;

(defun make-problem-from-clauses (clauses &key (gensymize t) &aux mapped-clauses  binding-map)
  (if gensymize
      (multiple-value-setq (mapped-clauses binding-map) (gensymize-vars clauses))
      (setq mapped-clauses clauses
	    binding-map nil))
  (loop 
     with new-problem = (make-problem)
     for objective in mapped-clauses
     for new-goal = (make-goal :objective objective)
     do
       (when debug* (print new-goal))
       (setf (goal-problem new-goal) new-problem)

     collect new-goal into goals
     when (positive-clause objective) collect objective into positives
     when (negative-clause objective) collect objective into negatives
       
     finally
       (setf (problem-goals new-problem) goals)
       (setf (problem-pos-objectives new-problem) positives)
       (setf (problem-neg-objectives new-problem) negatives)
       (setf (problem-objectives new-problem) (append positives negatives))
       (setf (problem-binding-map new-problem) binding-map)
       (return new-problem)))

(defun transfer-bindings-to-parent (problem)
  ;; appends any new bindings found for variables in the input problem to the binding environment in
  ;; the parent intention.  Translates between the naming spaces used in the problem and its parent.

  (let* ((parent (problem-i-parent problem))
	 (objectives (problem-objectives problem)))
    (format t "~&Transfering bindings ~A to parent intention" (problem-bindings problem))
    (format t "~&Using binding map ~A" (problem-binding-map problem))

    (when parent 
      (format t "~&Parent intention's bindings before: ~A" (intention-bindings parent))
      (append-to-place
       (map-all-bindings (collect-variables objectives) 
			 (problem-bindings problem)
			 (problem-binding-map problem)
			 (intention-bindings parent))
       (intention-bindings parent))
      (format t "~&Parent intention's bindings after: ~A" (intention-bindings parent))
      )))

;; *** will want a method of transfering bindings between intentions, child, and parent problems
;; *** during n-step lookahead.  Absent n-step lookahead, could still need this.  CHECK to see if
;; *** intentions ever return bindings found during execution.


(defun transfer-bindings-to-child (problem)
  ;; problem is the child, so transfer bindings from parent intention into child
  (let* ((parent (problem-i-parent problem))
	 (objectives (problem-objectives problem)))

    (format t "~&Transfering bindings ~A into child problem" (intention-bindings parent))
    (format t "~&Using binding map ~A" (problem-binding-map problem))

    (when parent 
      (format t "~&Parent intention's bindings before: ~A" (intention-bindings parent))
      (append-to-place
       (map-all-bindings (collect-variables (intention-conditions parent)) 
			 (intention-bindings parent)
			 (problem-binding-map problem)
			 (problem-bindings problem))
       (problem-bindings problem))
      (format t "~&Child problem's bindings after: ~A" (problem-bindings problem)))))

(defun make-problem-from-conditions (intention &aux sub-problem)
  (setq sub-problem
	(make-problem-from-clauses (intention-conditions intention)))
  (setf (problem-i-parent sub-problem) intention)

  ;; move exactly and only the necessary bindings from the intention across naming spaces into the child       
  (transfer-bindings-to-child sub-problem)   

  (print "Setting new active problem")
  (pprint-problem sub-problem)
  (setq active-problem* sub-problem))


(defun capture-bindings (opm problem)
  ;; installs the bindings found in opm in problem
  (setf (problem-bindings problem) (opmatch-bindings opm))
  (print "Bindings selected.")
  (print (problem-bindings problem))
  ;; FIX *** can this be made other than a flag?
  (setf (problem-bindings-selected? problem) t))

(defun problem-is-subset (sub p2)
  (let ((sub-objectives (csubst-bindings (problem-bindings sub) (problem-objectives sub)))
	(p2-objectives  (csubst-bindings (problem-bindings p2) (problem-objectives p2))))
    (clauselist-subset sub-objectives p2-objectives)))

(defun clauselist-subset (subset fullset)
  (loop for c in subset
       always (member c fullset :test #'unify)))

(defun get-problem-stack-above (problem)
  (let ((pstack (get-problem-stack problem)))
    (remove problem pstack :test #'eq)))

(defun well-formed (problem &aux res)
  ;; return T iff the problem is well-formed
  (setq res
	(or (null (problem-i-parent problem)) ; input problems are always well-formed
	    (problem-bindings problem))) ; as are problems with any bindings
  (if (null res) (format t "~&Problem ~A has no bindings" (problem-objectives problem)))
  res)




(defun flipped-clausep (c1 c2)
  ;; return true if the individual clauses c1 and c2 form a logical negation
  (cond ((negative-clause c1) (unify (cadr c1) c2))
	((negative-clause c2) (unify (cadr c2) c1))))

(defun flipped-filter (clause clauselist)
  (member clause clauselist :test #'flipped-clausep))

(defun flipped-problem-objectives? (problem)
  ;; returns true if problem contains any goals that are both false and the logical negation of any
  ;; goal up the stack.  

  ;; A problem is ill-formed if it attempts to accomplish something the system either intends to
  ;; undo, or relies on as true somewhere up the stack.

  (let* ((pstack (get-problem-stack-above problem))
	 (objectives (problem-objectives problem))
	 (bindings (problem-bindings problem))
	 (unsatisfied-clauses 
	  (find-unsatisfied-clauses (csubst-bindings bindings objectives))))
    (loop for p in pstack
	 for prior-objectives =  (csubst-bindings (problem-bindings p) (problem-objectives p))
	 thereis (any-flipped-clauses unsatisfied-clauses prior-objectives))))
	
(defun any-flipped-clauses (fromlist inlist)
  (loop for clause in fromlist
       thereis (flipped-filter clause inlist)))
       
(defun find-unsatisfied-clauses (clauses &optional bindings)
  (loop for c in clauses 
       when (equal icarus-fail (match-condition c cstm* bindings)) collect c))

(defun positive-part (clause)
  (if (negative-clause clause) (cadr clause) clause))

