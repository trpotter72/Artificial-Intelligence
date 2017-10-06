;; Daniel Shapiro 5/29/11
;; Functions for performing one step lookahead on the effects clauses associated with an executable intention

;; Perform lookahead with deductive closure over the effects in intention
;; Side effects cstm* and backpointers in cltm* in a big way. 
;; One-step-lookahead can only be undone by a next cycle of perception and inference.

;; Build the new belief model from scratch to ensure that inference
;; computes exactly and only the consequences of the hypothesized effects.

;; Effects may only encode basic beliefs (beliefs with no conceptual
;; substructure). This prevents inconsistencies in computing the deductive
;; closure over current beliefs.

;; Insist that positive effects have no free variables; can't hypothesize (on ?x B) for now
;; Allow negative effects to include free variables; the effect (not (on ?x B)) 
;; means no block will be on B

;;;;;;;;;;; 
(defparameter monotonic-progress-check* t)
;; if true, no intention can undo any goal required for any problem in the problem tree
;;;;;;;;;;

(defun one-step-lookahead (intention &aux (effects (get-instantiated-effects intention)))
  ;; Perform lookahead with deductive closure over the effects in intention
  ;; Side effects cstm* and backpointers in cltm* in a big way.
  ;; One-step-lookahead can only be undone by a next cycle of perception and inference.

  (let ((beliefs-to-hold (beliefs-from-effects (get-positive-effects effects)))
	(beliefs-not-to-hold
	 (find-all-matching-beliefs (get-positive-part (get-negative-effects effects)))))

    ;; Generate the deductive closure of current percepts given these
    ;; hypothetical changes. To do that:
    ;;   - clear cstm* and backpointers in cltm*
    ;;   - add beliefs-to-hold to cstm* with appropriate backpointers
    ;;   - run inference with the proviso that it cannot generate matches for beliefs-not-to-hold

    ;; clear cstm* and backpointers in cltm*
    (global-clear-beliefs)

    ;; add beliefs-to-hold into cstm* with appropriate backpointers
    (add-beliefs beliefs-to-hold)

    ;; unleash inference, but skip the perceptual processing step that
    ;; might filter OUT beliefs-to-hold since the items probably lack
    ;; a perceptual base

    ;; use standard inference in the lookahead computation because it was easier to modify with :avoidlist
    (let ((inference-method inference*))
      (setq inference* 'standard)
      (setq cstm* (infer  cltm* pstm* cstm* :avoidlist beliefs-not-to-hold))
;    (setq cstm* (chooser cltm* pstm* cstm* :avoidlist beliefs-not-to-hold))
      (setq inference* inference-method)
      cstm*)))

(defun find-all-matching-beliefs (clauses)
  ;; each clause can have multiple matches in memory
  (loop for clause in clauses
       append (find-beliefs-that-match clause)))

(defun get-positive-effects (effects)
  (filter effects #'positive-clause))

(defun get-negative-effects (effects)
  (filter effects #'negative-clause))

(defun find-beliefs-that-match (clause &optional (beliefs cstm*))
  (loop for belief in beliefs
       when (perfect-match clause belief)
       collect belief))

(defun perfect-match (clause belief)
  ;; do not accept a partial match of the clause against the belief
  ;; possibly change to satisfied-positive
  (eq (car (satisfied clause (list belief))) 'T))

(defun beliefs-from-effects (clauses &aux belief)
  ;; return a list of concept-instances that correspond to each clause
  ;; insist that the effects are fully-instantiated (can't hypothesize (on ?x B) for now)
  ;; and that they correspond only to basic concepts

  (loop for effect in clauses
       when (and (fully-instantiated effect) (lookup-basic-concept (car effect)))
       collect (belief-from-clause effect)))

(defun belief-from-clause (clause &optional (beliefs cstm*))
  ;; find the concept the clause corresponds to (insist it corresponds to a basic concept)
  ;; build a cinstance structure using the fully-intantiated clause for bindings
  (let ((c  (lookup-basic-concept (car clause)))
	(bindings nil)
	(new-belief nil))
    (cond (c
	   ;; This is an hypothesized concept instance, derive bindings
	   ;; from effects clause (which is fully instantiated here)
	   (setq bindings  (unify (concept-head c) clause))
	   (setq new-belief
		 (make-cinstance 
		  :head clause
		  :id (concept-id c)
		  :bindings bindings
		  ;; no positive dependencies since this is a basic concept
		  ;; no neg-dependencies since this is a basic concept
		  ;; no perceptual base since this is a projected belief
		  :percepts nil

		  ;; signal this is a projected belief
		  ;; removed before in the next round of inference
		  ;; from percepts.  Currently UNUSED.
;		  :projected t
		    )))
	  (t (format t "~&****no basic concept definition for clause, no belief returned")))
    new-belief))
  
(defun add-beliefs (beliefs)
  ;; adds the beliefs into memory with appropriate backpointers
  ;; side effects cstm* and cltm* in a big way
  (mapcar #'add-belief beliefs))

(defun add-belief (belief)
  ;; adds the belief into memory with appropriate backpointer in cltm*
  ;; side effects cstm* and cltm* in a big way
  (let ((concept (lookup-concept (cinstance-id belief))))
    (setf (concept-instances concept) (push belief (concept-instances concept)))
    (setf cstm*  (push belief cstm*))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; functions for determining if problem is advanced or made more complex given one-step-lookahead


(defun monotonic-progress (intention problem)
 ;; returns true if intention can be executed without undoing any goal achieved in any problem up
  ;; the tree NOTE: this is an aggressive monotonic progress strategy
  (if (not monotonic-progress-check*) t

      (let (problem-stack satisfied-goals-per-problem satisfied-goals-per-problem-after goals-undone)
	(setq problem-stack (get-problem-stack problem))

	;; collect all goals in the problem stack that are currently true (as a list of goal-lists by problem)
	(setq satisfied-goals-before
	      (loop for p in problem-stack collect (find-satisfied-goals p)))

	;; compute the future of the this intention
	(one-step-lookahead intention)

	;; collect all goals in the problem stack that are true given this intention executes
	(setq satisfied-goals-after 
	      (loop for p in problem-stack collect (find-satisfied-goals p)))
    
	;; report monotonic progress violations, if any
	(not (monotonicity-violations satisfied-goals-before satisfied-goals-after problem-stack intention)))))

(defun monotonicity-violations (goals-before goals-after problem-stack intention &aux goals-undone trouble)
  ;; goals-before, goals-after, and problem-stack are all lists of the same length

  ;; returns t if any goal unless some goal in goals-before is not in the corresponding
  ;; element of goals-after

  (format t "~&*****Checking intention ~A with effects ~A" 
	  (csubst-bindings (intention-bindings intention) (intention-head intention))
	  (csubst-bindings (intention-bindings intention) (intention-effects intention)))

  (format t "~&**************************projected beliefs*****************")
  (pretty-print-beliefs)
  (format t "~&")

  (print-problem-stack problem-stack)
  (loop 
       for gb in goals-before and
       for ga in goals-after and
       for p in problem-stack do

       (setq goals-undone (collect-goals-undone gb ga))
       (when goals-undone 
	 (format t "~&*****Intention undoes goals ~A in problem ~A" 
		 goals-undone
		 (csubst-bindings (problem-bindings p) (problem-objectives p)))
	 (setq trouble t)))

  (cond (trouble (format t "~&*****Intention fails") t)
	(t (format t "~&*****Intention passes monotonic progress test") nil)))

(defun get-problem-stack (problem)
  (cond ((null (problem-i-parent problem)) (list problem))
	(t (cons problem (get-problem-stack (intention-problem-parent (problem-i-parent problem)))))))

(defun get-problem-intention-stack (obj)
  (cond ((null obj) nil)
	((typep obj 'intention)
	 (cons obj (get-problem-intention-stack (intention-problem-parent obj))))
	((typep obj 'problem)
	 (cons obj (get-problem-intention-stack (problem-i-parent obj))))))

(defun print-problem-intention-stack (ls)
  (loop for obj in ls do
       (if (typep obj 'intention) (pprint-intention obj :selectors '(:head)))
       (if (typep obj 'problem) (pprint-problem obj :selectors '(:objectives)))))

(defun print-problem-stack (ps) 
  (loop for p in ps do 
       (format t "~&Problem objectives: ~A" (problem-objectives p))))

(defun collect-goals-undone (goalsbefore goalsafter)
  ;; returns nil if all goalsbefore are in goalsafter else returns a list of the goals undone
  (loop for goal in goalsbefore
     unless (member goal goalsafter :test #'equal) collect goal))


(defun acceptable-consequences (intention for-problem &aux problem)
  ;; return false if the intention, with lookahead and deductive
  ;; closure, causes any formerly satisfied goals in
  ;; problem to become untrue

;; here for temporary compatibility with old calling form, remove later
  (setq problem (get-top-level-problem for-problem) )

  (let (goals-satisfied-before goals-satisfied-after goals-undone)
    (setq goals-satisfied-before (find-satisfied-goals problem))
    (one-step-lookahead intention)
    (setq goals-satisfied-after (find-satisfied-goals problem))
    (setq goals-undone 
	  (loop for goal in goals-satisfied-before
	     unless (member goal goals-satisfied-after :test #'equal)
	     collect goal))

    (format t "~&*****Checking if consequences of intent ~A with effects ~A are acceptable"
		   (csubst-bindings (intention-bindings intention) (intention-head intention))
		   (csubst-bindings (intention-bindings intention) (intention-effects intention)))

    (format t "~&*****Top level satisfied goals before lookahead: ~A" goals-satisfied-before)
    (format t "~&*****Top level satisfied goals after lookahead: ~A" goals-satisfied-after)

    (format t "~&")
    (format t "~&**************************projected beliefs*****************")
    (pretty-print-beliefs)
    (format t "~&")

    ;; ensure that the next interpreter cycle recomputes state without relying on projected concepts 
    (undo-effects intention) 

    (cond (goals-undone
	   (format t "~&*******Intention ~A fails because it implies undoing goals ~A" 
		   (csubst-bindings (intention-bindings intention) (intention-head intention))
		  goals-undone)
	   nil)
	  ((not goals-undone) 
	   (format t "~&*****Intent ~A with effects ~A looks good" 
		   (csubst-bindings (intention-bindings intention) (intention-head intention))
		   (csubst-bindings (intention-bindings intention) (intention-effects intention)))
	   t))))

(defun get-top-level-problem (problem)
  ;; problems beget intentions, intentions beget problems
  (if (null (problem-i-parent problem))
      problem
      (get-top-level-problem (intention-problem-parent (problem-i-parent problem)))))

(defun find-satisfied-goals (problem)
    (loop for goal in (csubst-bindings (problem-bindings problem) 
				      (problem-objectives problem))
       when (goal-literal-satisfied? goal)
       collect goal))


(defun undo-effects (&optional intention)
  ;; use a club to clear beliefs and backpointers.  The next cycle of
  ;; inference will regenerate state from percepts.
    (global-clear-beliefs))

(defun get-instantiated-effects (intention)
  (csubst-bindings (intention-bindings intention)
		  (intention-effects intention)))


;;;;;;;;;;;; domain support functions
(defun positive-clause (clause) (not (negative-clause clause)))

(defun negative-clause (clause) (and clause (eq (car clause) 'not)))

(defun get-positive-part (clauses) 
  (loop for clause in clauses
       when (positive-clause clause) collect clause
       when (negative-clause clause) collect (cadr clause)))

(defun get-unchainable-conditions (clauses)
  ;; returns a list of the unchainable conditions in clauses
  (loop for c in clauses
       when (and (negative-clause c) (member (caadr c) neg-unchainable-conditions* :test #'eq))
       collect c

       when (and (positive-clause c) (member (car c) pos-unchainable-conditions* :test #'eq))
       collect c))

;; (defun fully-instantiated (clause)
;;   ;; true if the clause contains no variable
;;   (loop for sym in clause
;;        never (variable-p sym)))

(defun lookup-basic-concept (name)
  ;; returns the first definition for a basic concept in long term memory that matches name
  (loop for c in cltm* 
     when (and (eq name (concept-name c)) (basic-concept-p c))
     return c))

(defun basic-concept-p (concept)
  ;; returns true if this concept definition depends only upon percepts
  (if concept (null (concept-relations concept))))

;; (defun same-meaning (b1 b2)
;;   ;; beliefs encode the same meaning if their heads are fully-instantiated and match
;;   (let ((head1 (cinstance-head b1))
;; 	(head2 (cinstance-head b2)))
;;     (and (fully-instantiated head1)
;; 	 (fully-instantiated head2)
;; 	 (equal head1 head2))))

(defun get-basic-beliefs (&optional (beliefs cstm*))
  (loop for belief in beliefs
       when (basic-concept-p (lookup-concept (cinstance-id belief)))
       collect belief))

(defun lookup-concept (id)
  (loop for concept in cltm*
      do (if (eq id (concept-id concept)) (return concept)) ))

(defun extend-intention2 (intention bindings &aux new)
  ;; returns a new intention with content identical to the previous,
  ;; except with bindings extended
  (setq new (copy-structure intention))
  (setf (intention-bindings new) (append bindings (intention-bindings new)))
  new)

(defun extend-intention (intention bindings)
  ;; add bindings to the intention structure and return it
  (setf (intention-bindings intention) (append (intention-bindings intention) bindings))
  intention)
 


;;;;;;;;;;;; utilites

(defun filter (ls fn)
  ;; utility returns a list whose elements survive the filter function, fn
  (loop for item in ls
       when (funcall fn item)
       collect item))

(defun print-beliefs (&optional (mem cstm*))
  (loop for belief in mem do (print (cinstance-head belief))))



;;;;;;;; test code

(defun test-projection (beliefs-to-hold beliefs-not-to-hold)
  ;; the inputs had better be basic beliefs

  (global-clear-beliefs)
  (setq cstm* beliefs-to-hold)

  (format t "~2&***** Beliefs at the start of projection ********")
  (print-beliefs cstm*)

  (format t "~2&***** Beliefs to avoid ********")
  (print-beliefs beliefs-not-to-hold)

  ;; compute deductive closure the right way for projected beliefs
  (setq inference* 'STANDARD)
  (setq cstm* (infer cltm* pstm* cstm* :avoidlist beliefs-not-to-hold))

  (format t "~2&*****Beliefs after deductive closure" )
  (print-beliefs cstm*))



