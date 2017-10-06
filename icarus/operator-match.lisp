;; Operator-match.lisp 
;; dgs 2/22/12 

;; The opmatch abstraction represents the partial match of a skill or a concept on both goals and
;; beliefs, and provides operations for computing that match.

;;;;;;;;;;;;;;;;;

(defun has-norvig-bindings (res)
  ;; return true if res represents a non-empty norvig binding set
  (and (not (equal res fail))
       (listp res)
       (not (equal res no-bindings))))

(defun norvig-bindings (res)
  ;; return the bindings in res, with nil overloaded to represent fail and empty
  (cond ((equal res fail) nil)
	((equal res no-bindings) nil)
	(t res)))

(defun negated-literal (form) (and (listp form) (eq (first form) 'not)))
(defun positive-literal (form) (and (listp form) (not (eq (first form) 'not))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           opmatch

;; an opmatch (short for operator match) represents the partial match of a skill or non-primitive
;; concept against outstanding goals and beliefs. For skills, effects match against goals, and
;; conditions match on beliefs.  For concepts, the head matches against goals, while the relations
;; match onto beliefs.  This code uses the hopefully neutral term "postconditions" for
;; effects/concept heads, and "preconditions" for conditions/relations.

;; Opmatch structures accumulate bindings, track the postconditions and preconditions
;; still to be tested, and record matched postconditions, preconditions, and goals.

;; 
(defstruct opmatch 
  problem                      ;; The problem motivating this search for an operator match.
  operator                     ;; A non-primitive concept or skill.
  bindings                     ;; Contains the accumulated binding environment for the partial match.
                               ;; The match process does NOT substitute bindings into the
                               ;; preconditions, postconditions, and goals fields.

  preconditions-to-go          ;; to-go means untested so far
  preconditions-matched        ;; matched means the clause unified under some bindings
  preconditions-unmatched      ;; unmatched means the clause was tested but did not unify under any bindings
  postconditions-to-go
  postconditions-matched
  postconditions-unmatched

  goals-matched                ;; goals are match targets.
  goals-unmatched            ;; All goals begin as not-matched. Some  migrate to the matched category.

  score)                       ;; Partial matches can carry a score calculated by a heuristic function.

;; opmatch operations

;; FIX TO HANDLE CHAINED BINDINGS
(defun create-opmatch (op problem &aux new)
  ;; returns an opmatch structure that initializes a partial match
  ;; cases appropriately on the type of the operator
  (setq new
	(make-opmatch
	 :problem problem
	 :operator op ;; a non-primitive concept or skill

	 ;; Substitute in any bindings passed down from external contexts
	 :goals-unmatched (csubst-bindings (problem-bindings problem) (problem-objectives problem))))

  (cond ((typep op 'concept)
	 (setf (opmatch-postconditions-to-go new) (list (concept-head op))
	       (opmatch-preconditions-to-go new) (concept-relations op)))
	((typep op 'sclause)
	 (setf  (opmatch-postconditions-to-go new) (sclause-effects op)
		(opmatch-preconditions-to-go new) (sclause-conditions op))))
  new)

(defun next-opmatch (opm)
  ;; selects among partial matches en-route to finding maximal matches
  (let* ((successors (successors-to-opmatch opm))
	 (res (if successors (random-choose successors))))
    res))

(defun successors-to-opmatch (opm)
  ;; Advances the partial operator match in opm by testing postconditions against goals,
  ;; then testing preconditions against belief memory.

  ;; Returns a list of opmatch structures that advance the partial match, or nil if no
  ;; postconditions and no preconditions left to match.

  ;; Advance the partial match by attempting to match one clause.  This may match onto goals or
  ;; beliefs, and may generate more bindings. At minimum, the step will consume one clause.

  (cond ((null opm) nil)
	((opmatch-postconditions-to-go opm)
	 (match-postcondition-on-goals opm))
	((opmatch-preconditions-to-go opm)
	 (match-precondition-on-beliefs opm))
	;; nothing left to work on so return nil
	(t nil)))

(defun match-postcondition-on-goals (opm)
  ;; Matches the next postcondition against all unmatched goals, and returns a list of opmatch
  ;; structures found, or nil.

  (let* ((postconditions (opmatch-postconditions-to-go opm))
	 (goals (opmatch-goals-unmatched opm))
	 (condition (first postconditions))
	 (bindings  (opmatch-bindings opm))
	 (res nil)
	 (matches nil)
	 (target nil))

    ;; Collect each match (singular) of this condition on a goal.  Retrieve
    ;; bindings from matching positive and negative postconditions on goals.

    ;; if Goals= (on A B)(on B C), postcond = (on ?x ?y), want to mark postcond matched and
    ;; retrieve alternate bindings

    ;; if Goals = (not (on A B)) (not (on C B)), postcond= (not (on ?any B)), want to mark
    ;; postcond as matched and either (1) retrieve alternate bindings, or (2) mark both goals
    ;; as matched but retrieve no bindings
    ;; This code implements (1)


    (loop for goal in goals do
	 ;; handle the boundary case of null bindings by accessing the norvig unification default
	 (if (and (typep (opmatch-operator opm) 'concept) (negative-clause goal))
	     ;; operators representing concepts only match onto the positive part of goals
	     (setq target (second goal))
	     (setq target goal))

	 (setq res (if bindings (unify condition target bindings) (unify condition target)))

       when (equal res no-bindings) ;; a match with no bindings
       collect (advance-opmatch opm :matched-postcondition condition :matched-goal goal)
         into matches

       when (has-norvig-bindings res)
       collect (advance-opmatch opm :matched-postcondition condition 
				    :matched-goal goal 
				    :bindings (norvig-bindings res))
	 into matches
	      
       finally (if matches
		   (return matches)
		   (return (list (advance-opmatch opm :unmatched-postcondition condition)))))))

(defun match-precondition-on-beliefs (opm &optional (mem cstm*))
  ;; matches the next precondition on belief memory and returns a list of opmatch
  ;; structures that capture each advance to the partial match found.

  (let* ((preconditions (opmatch-preconditions-to-go opm))
	 (goals (opmatch-goals-unmatched opm))
	 (condition (first preconditions))
	 (bindings  (opmatch-bindings opm)))

    (cond ((negated-literal condition)
	   ;; NEED a function that extracts the positive clause internal to the negation,  matches onto
	   ;; all clauses in CSTM, and returns the first set of bindings it finds, or icarus-fail if none.

	   (let ((res (match-negative-condition condition mem bindings)))
	     (if (equal res icarus-no-bindings)
		 ;;<x> in (not <x>) does not match onto beliefs, so this is a success 
		 (list (advance-opmatch opm :matched-precondition condition))

		 ;;<x> in (not <x>) matches onto beliefs, so this is a failure
		 (list (advance-opmatch opm :unmatched-precondition condition)))))

	  ((positive-literal condition)
	   ;; NEED a function that employs bindings without substituting them in first, matches onto
	   ;; all clauses in CSTM, returns all matches found, and refuses to bind the same object to
	   ;; two variables.  THIS DOES NOT SEEM TO EXIST!!

	   (let ((res (match-positive-condition condition mem bindings)))
	     (cond ((equal res icarus-fail)
		    ;; precondition does not match onto beliefs
		    (list (advance-opmatch opm :unmatched-precondition condition)))

		   ((equal res icarus-no-bindings)
		    ;;precondition matches one belief exactly (no new bindings)
		    (list (advance-opmatch opm :matched-precondition condition)))

		   ((has-icarus-bindings res)
		    ;;res could contain many matches that need to be saved
		    (loop for binding in res
		       collect (advance-opmatch opm :matched-precondition condition :bindings binding)))))))))

(defun advance-opmatch (opm
			&key bindings new-bindings matched-goal matched-postcondition matched-precondition
			     unmatched-postcondition unmatched-precondition)

  (let ((newopm (copy-structure opm)))
   (if bindings (setf (opmatch-bindings newopm) bindings))                    ;; replace the bindings in newopm
   (if new-bindings (append-to-place new-bindings (opmatch-bindings newopm))) ;; augment the bindings in new-opm

   (if matched-goal
       (move-to-place matched-goal (opmatch-goals-unmatched newopm) (opmatch-goals-matched newopm)))
   (if matched-postcondition
       (move-to-place matched-postcondition (opmatch-postconditions-to-go newopm) (opmatch-postconditions-matched newopm)))
   (if unmatched-postcondition
       (move-to-place unmatched-postcondition (opmatch-postconditions-to-go newopm) (opmatch-postconditions-unmatched newopm)))
   (if matched-precondition 
       (move-to-place matched-precondition (opmatch-preconditions-to-go newopm) (opmatch-preconditions-matched newopm)))
   (if unmatched-precondition 
       (move-to-place unmatched-precondition (opmatch-preconditions-to-go newopm) (opmatch-preconditions-unmatched newopm)))
   newopm))

(defun same-opmatch (c1 c2)
  ;; Two operator matches are equivalent if they concern the same operator and have the same
  ;; bindings.  Does not consider the state of the match (e.g., that the postconditions-to-go and
  ;; preconditions-to-go are equal.
  (and (eq (opmatch-operator c1) (opmatch-operator c2))
       (same-bindings (opmatch-bindings c1) (opmatch-bindings c2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; opmatch scoring 

;; Cleaner to define a function that takes a list of placenames and collects lengths from opmatch
;; structures, and values from the heuristic, then takes the dot product

(defun collect-field-lengths (obj &rest fieldnames)
  (loop for name in fieldnames collect (length (slot-value obj name))))

(defun collect-field-values (obj &rest fieldnames)
  (loop for spec in fieldnames collect (slot-value obj spec)))

(defun score-opmatch2 (opm)
  (let* ((bob opmatch-heuristic*)
	 (fieldnames (list 'goals-matched 'goals-unmatched 
			   'postconditions-matched 'postconditions-unmatched
			   'preconditions-matched 'preconditions-unmatched
			   )))

    ;; assumes that heuristics and opmatch objects have fields with the same names
    (dotproduct (collect-field-lengths opm fieldnames)
		(collect-field-values bob fieldnames))
  ))

(defun dotproduct (a b) (apply #'+ (mapcar #'* a b)))

(defun score-opmatch (opm)
  (let ((gm (length (opmatch-goals-matched opm)))
	(gu (length (opmatch-goals-unmatched opm)))
	(postcm (length (opmatch-postconditions-matched opm)))
	(postcu (length (opmatch-postconditions-unmatched opm)))
	(precm (length (opmatch-preconditions-matched opm)))
	(precu (length (opmatch-preconditions-unmatched opm)))
;;	(pgs (percent-goals-solved candidate))
;;	(pca (percent-conditions-actionable candidate)))

	(bob opmatch-heuristic*))
  (setf (opmatch-score opm) 
	(+ 
	 (* gm (heuristic-goals-matched bob))
	 (* gu (heuristic-goals-unmatched bob))
	 (* postcm (heuristic-postconditions-matched bob))
	 (* postcu (heuristic-postconditions-unmatched bob))
	 (* precm (heuristic-preconditions-matched bob))
	 (* precu  (heuristic-preconditions-unmatched bob))

;;	 (* pgs (heuristic-percent-goals-solved bob))
;;	 (* pca (heuristic-percent-conditions-actionable bob))
	 ))

  (cond (dgs-debug*
	 (format t "~2&Candidate: ~A" opm)
	 (format t "~&Weights::Counts")
	 (format t "~&   Goals matched ~A::~A Goals unmatched ~A::~A Conditions matched ~A::~A Conditions unmatched ~A::~A"
		 (heuristic-goals-matched bob) gm
		 (heuristic-goals-unmatched bob) gu
		 (heuristic-postconditions-matched bob) postcm
		 (heuristic-postconditions-unmatched bob) postcu)))

;;	 (format t "~&   Percent-goals-solved ~A::~A Percent-conditions-actionable ~A::~A Score ~A"
;;		 (heuristic-percent-goals-solved bob) pgs
;;		 (heuristic-percent-conditions-actionable bob) pca
;;		 (opmatch-score candidate))
))


(defun opmatch-score> (candidate1 candidate2)
  (> (opmatch-score candidate1) (opmatch-score candidate2)))

(defun opmatch-score< (candidate1 candidate2)
  (< (opmatch-score candidate1) (opmatch-score candidate2)))
