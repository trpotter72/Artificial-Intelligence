;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; solver-utilities.lisp
;; for skill selection and problem solving
;; dgs 1/11/2012
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  Global variables for problem solver
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defparameter problem-solver-enabled* t)
(defparameter active-problem* nil)
(defparameter executing-intention* nil)
(defparameter constraint-memory* nil)
(defparameter pos-unchainable-conditions* nil)
(defparameter neg-unchainable-conditions* nil)
(defparameter prior-executing-intention* nil) ;; history information for problem solver
(defparameter problem-tree-history* nil) ;; keeps prior problem trees
(defparameter flush-problem-tree* t) ;; causes current top level problem to refresh after executing a step


(defvar dgs-debug* nil)
(defparameter debug-failure-contexts* t)


;;FIX THIS TO PICK A HEURISTIC INSTEAD ***

;; There are three possible options for this global switch:
;;    1. :BACKWARD (default)
;;    2. :FORWARD
(defparameter search-direction* :BACKWARD)

;; There are three possible options for this global switch:
;;    1. :MAX-EFFECTS-MATCHED (default)
;;    2. :MIN-UNSATISFIED-CONDITIONS
;;    3. :BOTH-1-2 (yet to be implemented)
(defparameter skill-selection-heuristic* :MIN-UNSATISFIED-CONDITIONS)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; icarus binding utilities
(defconstant icarus-fail '(nil))
(defconstant icarus-no-bindings '(T))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; macros

(defmacro append-to-place (item place) `(setf ,place (append ,item ,place)))

(defmacro move-to-place (item old new)
  `(progn  
     (setf ,old (remove ,item ,old))
     (setf ,new (cons ,item ,new))))

(defmacro place-length (place) `(if (listp ,place) (length ,place)))

;;;;;;;;;;;;;;;;;;;;;;
(defun has-icarus-bindings (b) (and (not (equal b icarus-fail)) (not (equal b icarus-no-bindings))))

(defun ill-formed-binding-list (bindings)
  ;; return t if any two variables are bound to the same object, or the same var is bound more than once
  (cond ((null bindings) nil)
	((ill-formed-var-binding (first bindings) (rest bindings))
	 t)
	(t (ill-formed-binding-list (rest bindings)))))

(defun ill-formed-var-binding (binding bindingset)
  (cond ((null bindingset) nil)
	((same-varpart binding (first bindingset))
	 (if dgs-debug* 
	     (format t "~&The same variable bound twice: ~A to ~A and ~A in ~A" 
		     (car binding) (cdr binding) (cdr (first bindingset)) bindingset))
	 t)
	((same-valpart binding (first bindingset))
	 (if dgs-debug*
	     (format t "~&The same object is bound to two variables: ~A to ~A and ~A in ~A" 
		     (cdr binding) (car binding) (car (first bindingset)) bindingset))
	 t)
	(t (ill-formed-var-binding binding (rest bindingset)))))

(defun same-varpart (b1 b2)
  ;; b1 and b2 are bindings
  (eq (car b1) (car b2)))

(defun same-valpart (b1 b2)
  (eq (cdr b1) (cdr b2)))

(defun same-bindings (b1 b2)
  (cond ((null b1)(null b2))
	;; contents had better match
	(t (loop for binding in b1 always (member binding b2 :test #'equal)))))

;; substitues the possibly chained value of a variable in generic, and quotes it
(defun norvig-qsubst-bindings (bindings generic)
  (let ((form generic)
	(pair nil))
    (loop for bd in bindings do
	 (setq pair (get-final-binding (car bd) bindings))
	 (if pair
	     ;; substitue the quoted chained value of the variable in bd into form
	   (setq form (subst  (list 'quote  (cdr pair)) (car bd) form))))
    form))

(defun csubst-bindings (bindings generic)
  (let ((form generic)
	(pair nil))
    (loop for bd in bindings do
	 (setq pair (get-final-binding (car bd) bindings))
	 (if pair
	     ;; substitue the chained value of the variable in bd into form
	   (setq form (subst (cdr pair) (car bd) form))))
    form))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; infrastructure for hueristic skill selection

;; a heuristic holds relative weights on features derived from skillmatches.  Weights default to zero.
(defstruct heuristic
  name
  (goals-matched  0)
  (goals-unmatched 0)
  (postconditions-matched 0)
  (postconditions-unmatched 0)
  (preconditions-matched 0)
  (preconditions-unmatched 0)
  )

;; only care about reducing goals, but use matched preconditions as a tie breaker
(defparameter extreme-backward-progress*
  (make-heuristic :goals-matched 1000 :preconditions-matched 10  :name  'extreme-backward-progress*))

;; only care about matching preconditions, ignoring goal progress
(defparameter extreme-forward-progress*
  (make-heuristic :preconditions-matched 100 :preconditions-unmatched -100 :name  'extreme-forward-progress*))

(defparameter even-handed*
  (make-heuristic :goals-matched 1 :preconditions-matched 1 :preconditions-unmatched -1 :name 'even-handed*))

(defparameter goalmatch-above-condition-progress2*
  (make-heuristic :goals-matched 2 :preconditions-matched 1 :preconditions-unmatched -1 :name 'goalmatch-above-condition-progress2*))

(setq opmatch-heuristic* extreme-backward-progress*)


;;;;;;;;;;;; 
;; heuristic skill selection functions
(defun operator-selection-heuristic (candidates &aux res)
  (loop for candidate in candidates do (score-opmatch candidate))
  (setq res (sort candidates #'opmatch-score<))

  ;; extract list of scores
  (setq scores (loop for c in candidates collect (opmatch-score c)))
  (probabilistically-select res scores))

(defun probabilistically-select (items scores  &aux draw)
  ;; items and scores are matched one for one.  Scores are in ascending order.
  ;; selects and returns an item from items with probability proportional to its score

  (let* ((shifted-scores (shift scores (1+ (* -1 (apply #'min scores))))) 
	 ;; shift scores to the range (1 max+min+1).  This defines 1 as the minimum score.

	 (normalized-scores (normalize shifted-scores))
	 (cumulative-scores (cumulative-distribution normalized-scores))
	 (draw (random 1.0)))

;    (if dgs-debug* (loop for i below (length items) 
;		      do (format t "~& Item: ~A ~&Score: ~A" (nth i items) (nth i scores))))

	  ;; select the first item from the cumulative distribution that beats a random number in (0 1)
     (nth  (position-if-above cumulative-scores draw) items)))

;;;;;;;;;;;;;;;;;;;;;;;
;; mathematics for interpreting scores as probabilities

(defun shift (scores k) (loop for s in scores collect (+ s k)))

(defun scale (scores minscore maxscore)
  ;; scales scores to the (0 1) range, where minscore maps to 0 and maxscore maps to 1
  (let* ((a (/ 1 (- maxscore minscore)))
	 (b (* a minscore)))
    (loop for s in scores collect (- (* a s) b))))

(defun normalize (scores)
  (let ((m (apply #'+ scores)))
    (loop for s in scores collect (/ s m))))

(defun cumulative-distribution (scores)
  ;; assumes scores are in increasing order and normalized
  (loop for s in scores 
     sum s into running-total
       collect running-total))

(defun position-if-above (scores draw)
    (loop for i below (length scores) by 1
	 when (>= (nth i scores) draw)
	 return i))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;
;; Iterative Sampling Search Mechanism

;; fix to  make depth-limit and other parameters optional to extent possible***
(defun false-fn (&rest ignore) nil)

(defun iterative-sampling-search (node next-fn 
				  &key (successp #'false-fn) (failurep #'false-fn)
				       (max-trials 10) (depth-limit 100)
				  &aux res)
  ;; iterative sampling is depth first search with rewind to top on failure.  It conducts
  ;; the depth-first search maxtrials times, and bounds the depth of each trajectory to
  ;; depth-limit.  

  ;; The function next-fn is a node generator; (<next-node> node) must produce a succesor
  ;; node, or nil.  It should have a probabilistic quality for iterative
  ;; sampling to make much sense.  The parameters successp, failurep are functions of one
  ;; node with the obvious meaning.  A given depth-first search terminates when either is
  ;; true.

  ;; Input should be a non-nil node that supports the next-fn operator.
  ;; Returns nil iff input is nil, otherwise returns a list containing leaf nodes of the search as:
  ;;      (successfull-nodes failed-nodes limit-nodes terminal-nodes)
  ;; where (<successp> successfull-node) = T, (<failurep failed-node)=T, 
  ;; both predicates are false for a limit node, which was additionally found at the search depth limit, and
  ;; (<next-fn> terminal-node) = nil.


    (loop for n below max-trials
       do
       (setq res (depth-first-search node next-fn successp failurep depth-limit))
	 when (first res) collect it into successfull-nodes
	 when (second res) collect it into failed-nodes
	 when (third res) collect it into limit-nodes
	 when (fourth res) collect it into terminal-nodes
       finally  
	 (if dgs-debug* 
	     (format t "~&Iterative sampling results: ~&  Success: ~A~&  Failed: ~A~&  Limit-nodes ~A~&  Terminal-nodes: ~A"
		     successfull-nodes failed-nodes limit-nodes terminal-nodes))
	 (return  (list successfull-nodes failed-nodes limit-nodes terminal-nodes))))

(defun depth-first-search (node next-fn successp failurep depth-to-go &aux nextnode)
  (cond ((null node) nil)
	((funcall successp node) (list node nil nil nil))
	((funcall failurep node) (list nil node nil nil))
	((<= depth-to-go 0) (list nil nil node nil))
	(t (setq nextnode (funcall next-fn node))
	   (if nextnode 
	     (depth-first-search nextnode next-fn successp failurep (1- depth-to-go))
	     (list nil nil nil node)))))

(defun successfull-nodes (res) (and res (first res)))
(defun failed-nodes (res) (and res (second res)))
(defun limit-nodes (res) (and res (third res)))
(defun terminal-nodes (res) (and res (fourth res)))

;;;;; skill instance - a simple cons of a skill and bindings

(defun skill-part (skill-instance) (car skill-instance))
(defun bindings-part (skill-instance) (cdr skill-instance))
(defun create-skill-instance (s b) (cons s b))

;;;;;;;;;;;;
;; test hrness for iterative sampling search
(defun nextnum (n &aux res) (setq res (round (+ (random 10) n))) (if (> res 55) nil res))
(defun winner (n) (> n 50))
(defun winner2 (n) (> n 70))
(defun loser (n) (and (< n 24) (> n 21)))
;; (iterative-sampling-search 1 #'nextnum :successp #'winner :failurep #'loser :max-trials 10 :depth-limit 10)

;;(defun iterative-sampling-search (node next-fn successp failurep max-trials depth-limit &aux res)

