;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;previously defined in holdover.lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Global variables, Initializations and Functions from 
;;; interpreter.lisp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar cycle*)
(defvar starttime*)
(defvar pstm*)
(defvar cstm*)
(defvar astm*)

(defvar halt*)
(defvar failed*)

(defvar gtrace*)
(defvar ptrace*)
(defvar btrace*)
(defvar ctrace*)
(defvar atrace*)
(defvar etrace*)

;Switch for debug mode
(defvar debug*)

(defvar inference*)

;The threshold for degree of match below which the system would not
; print out the belief.
(defparameter belief-printout-threshold* 0.5)

(setq cycle* 0)
(setq gtrace* t) ; goal print
(setq ptrace* 1) ; 1 for organized print, and 2 for raw print of percepts
(setq btrace* t) ; belief print
(setq ctrace* t) ; cycle print
(setq atrace* t) ; action print
(setq etrace* t) ; 

(setq debug* nil)

;*** Switch for Inference Mechanism ***
; STANDARD : standard matcher (INFER)
; FAST     : fast matcher (RUN-INFERENCE)
(setq inference* 'standard)

; RUN executes the Icarus interpreter for N cycles or, if called without 
; an argument, indefinitely. 
(defun run (&optional (n -1))
  (setq halt* nil)
  (run-init)
  (run-aux (1+ n)))

; RUN executes the Icarus interpreter for N cycles or until all top-level 
; goals are satisfied. If called without an argument, the system runs
; indefinitely until all goals are satisfied. 

(defun grun (&optional (n -1))
  (setq halt* nil)
  (run-init)
  (run-aux (1+ n)))

(defun grun1 ()
  (setq halt* nil)
  (run-init))


; CONT does the same as RUN, except it does not reinitialize variables
; or the environment. 

(defun cont (&optional (n -1))
  (setq halt* nil)
  (run-aux (+ cycle* n)))

; GCONT does the same as GRUN, except it does not reinitialize variables
; or the environment. 

(defun gcont (&optional (n -1))
  (setq halt* nil)
  (run-aux (+ cycle* n)))

(defun timed-grun (timelimit)
  (setq halt* nil)
  (run-init)
  (run-aux 0 :timelimit timelimit))

; RUN-INIT initializes global variables and the state of the simulated
; environment in preparation for an Icarus run. 
(defun run-init ()
  (setq cycle* 1)
  (setq starttime* (get-universal-time))
  (setq new-skills* nil)
  (setq new-concepts* nil)
  (setq pstatetrace* nil)
  (setq cstatetrace* nil)
  (setq skilltrace* nil)
  (setq failcount* 0)

  (cond ((equal inference* 'fast)
	 (clear-fast-matcher)))

  (init-eltm)

;  (if (fboundp 'initialize-world)
;      (initialize-world)
;    (error "INITIALIZE-WORLD function is not defined.~%Make sure the simulator has the definition."))
  (print-icarus-settings))

(defun check-essential-functions ()
  (cond ((and (equal inference* 'STANDARD)
	      (not (fboundp 'infer)))
	 (error "INFER function is not defined.~%Make sure you are loading MATCHER.LISP."))
	((and (equal inference* 'FAST)
	      (not (fboundp 'run-inference)))
	 (error "RUN-INFERENCE function is not defined.~%Make sure you are loading the fast matcher.")))

  (if (not (fboundp 'update-world))
      (error "UPDATE-WORLD function is not defined.~%Make sure the simulator has the definition.")))

(defun print-setting (param &rest options)
  (cond ((null options)
	 (if (null param) (princ "OFF") (princ "ON")))
	(t
	 (let (setting)
	   (mapcar #'(lambda (option)
		       (if (equal (car option) param)
			   (setq setting (cadr option))))
		   options)
	   (if (null setting) (princ "UNKNOWN") (princ setting))))))

(defun print-memory-traces ()
  (cond ((not (null ctrace*))
	 (terpri)(princ "----------")
	 (terpri)(princ "Cycle ")(princ cycle*)))
  (cond ((not (null gtrace*))
	 (print-problems)))
  (cond ((equal ptrace* 2)
	 (print-percepts T))
	((equal ptrace* 1)
	 (print-percepts)))
  (cond ((not (null btrace*))
	 (pretty-print-beliefs)))
  nil)

(defun variablep (sym-name)
 (cond ((atom sym-name)
	(cond ((numberp sym-name)
	       nil)
	      (t
	       (eq (elt (symbol-name sym-name) 0) #\?))))))

(defun rcopy (x)
  (cond ((atom x) x)
        (t (mapcar #'rcopy x))))

(defvar max-length-print-full-percept* 40)   ;; Glenn - Was 2, made it to 40.

(defun print-percepts (&optional (raw nil) &aux (localpercepts))
  ;; do setf so will work in SBCL
  (setf localpercepts (sort (copy-list pstm*) #'string< :key #'car))
  (terpri)(princ "Percepts:")
  (cond (raw (pprint localpercepts))
	(t
	 (let ((last nil))
	   (mapcar #'(lambda (percept)
		       (cond ((or (null last)
				  (not (equal (car percept) last)))
			      (setq last (car percept))
			      (terpri)(princ "   ")(princ last)(princ ":")
			      (terpri)(princ "      ")
			      (cond ((> (length percept)
					max-length-print-full-percept*)
				     (princ "(")
				     (mapc
				      #'(lambda (element)
					  (princ element)
					  (princ " "))
				      (subseq percept
					      0
					      max-length-print-full-percept*))
				     (princ "...)"))
				    (t
				     (princ percept))))
			     (t
			      (terpri)(princ "      ")
			      (cond ((> (length percept)
					max-length-print-full-percept*)
				     (princ "(")
				     (mapc
				      #'(lambda (element)
					  (princ element)
					  (princ " "))
				      (subseq percept
					      0
					      max-length-print-full-percept*))
				     (princ "...)"))
				    (t
				     (princ percept))))))
		   localpercepts)))))

(defun pp () (print-percepts))

(defun pretty-print-beliefs (&aux (localcstm))
  (setf localcstm (sort (copy-list cstm*) #'string< :key #'cinstance-name))
  (terpri)(princ "Beliefs:")
  (if (null localcstm) (princ " NONE")
      (let ((last nil))
	(mapcar #'(lambda (belief)
		    (let* ((name (cinstance-name belief))
			   (head (cinstance-head belief))
			   (listform (subst-bindings
				      (head-bindings head)
				      (head-listform head)))
			   (degmatch (cinstance-degmatch belief)))
		      (unless (and (numberp degmatch)
				   (< degmatch belief-printout-threshold*))
			(cond ((or (null last)
				   (not (equal name last)))
			       (setq last name)
			       (terpri)(princ "   ")(princ last)(princ ":")
			       (terpri)(princ "     ")(princ listform)
			       (cond ((numberp degmatch)
				      (cond ((< degmatch 1.0)
					     (princ " ")(princ degmatch))
					    ((= degmatch 1.0))
					    (t
					     (princ " * INVALID DEGMATCH *"))))
				     (t
				      (princ " * NO DEGMATCH *"))))
			      (t
			       (terpri)(princ "     ")(princ listform)
			       (cond ((numberp degmatch)
				      (cond ((< degmatch 1.0)
					     (princ " ")(princ degmatch))
					    ((= degmatch 1.0))
					    (t
					     (princ " * INVALID DEGMATCH *"))))
				     (t
				      (princ " * NO DEGMATCH *"))))))))
		localcstm)))
  T)

(defun pb () (pretty-print-beliefs))

(defun print-concepts ()
  (terpri)(princ "Concepts:")(terpri)
  (mapc #'(lambda (c) (print-concept c)(terpri)) cltm*) 
  nil)

(defun print-concept (concept)
  (terpri)(princ "(")(princ (concept-head concept))
  (terpri)(princ " :percepts  ")(princ (concept-percepts concept))
  (cond ((not (null (concept-relations concept)))
	 (terpri)(princ " :relations ")(princ (concept-relations concept))))
  (cond ((not (null (concept-tests concept)))
	 (terpri)(princ " :tests     ")(princ (concept-tests concept))))
  (princ ")"))

(defun pc () (print-concepts))

; SATISFIED inputs a single goal element, with or without unbound 
; variables, and a list of memory elements from CSTM*. The function 
; returns ( flag . bindings ) form, where flag is T if the goal
; is satisfied and NIL otherwise. It calls on
; different functions depending on whether the goal is positive 
; (e.g., (on ?X B)) or negative (e.g., (not (on ?X B))). 
;  NOTE: the bindings represent the match found, in the case
;        of negative literal not satisfied, bindings is the match that 
;        was found that made the negative literal unsatisfied.

(defun satisfied (goal cstm)
  (if (null goal) (list T)
    (cond ((eq (car goal) 'not)
	   (satisfied-negative (cadr goal) cstm))
	  (t (satisfied-positive goal cstm)))))

;TLP_EXP - now it checks if the goal concept is partially matched or not.
; SATISFIED-POSITIVE inputs a positive goal element like (on ?X B) 
; and a list of memory elements from CSTM*. It returns T if the list 
; contains an element that matches the goal with the degree of match of 1.0.
; If the goal is partially matched, it returns the degree of match. Otherwise it
; returns nil.

(defun satisfied-positive (goal cstm)
  (let (result flag)
    (do ((i 0 (1+ i)))
	((or (equal i (length cstm))
	     flag)
	 result)
      (setq result (bmatches goal (nth i cstm) nil))
      (setq flag (car result)))))

;TLP_EXP: modified to return nil if there is a matching concept instance
; with full degree of match, T if there is no such concept instance (fully or
; partially matched), and the maximum degree of match if there is only partially
; matched concept instances.
; SATISFIED-NEGATIVE inputs a negative goal element like (not (on ?X B)) 
; and a list of memory elements from CSTM*. It returns T if the list 
; does NOT contain any elements that match the goal expression and NIL
; if the list contains one or more elements that match the expression with
; the degree of match 1. It returns (1-max. degree of match) if the list
; contains only such expressions with partial degree of match.

(defun satisfied-negative (goal cstm)
  (let ((flag T)
	max max-result result)
    (do ((i 0 (1+ i)))
	((or (equal i (length cstm))
	     (null flag))
	 (cond ((null flag) (cons flag (cdr result)))
	       ((numberp max) (cons (- 1 max) (cdr max-result)))
	       (t (list flag))))
      (setq result (bmatches goal (nth i cstm) nil))
      (cond ((numberp (car result))
	     (cond ((and (numberp max)
			 (> (car result) max))
		    (setq max (car result))
		    (setq max-result result))
;		   ((not (numberp max))
		   ((null max)
		    (setq max (car result))
		    (setq max-result result))))
	    ((car result)
	     (setq flag nil))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;previously defined in changed.lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; This file has functions from the old code that have been
;;; modified to some degree to make them compatible.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun quote-constants (action)
;  (mapcar #'quote-constants-aux action)
  (cond ((null action) nil)		; added so that when list is NIL, this returns NIL instead of (NIL)
	(t (quote-constants-aux action))))

; QUOTE-CONSTANTS-AUX takes a list and returns the list with all the constants
; quoted for later evaluation. It assumes that the first element of the list
; is a function name, and therefore does not quote it. This may not be necessary
; because the function name can be evaluated too, but it is there anyway.
(defun quote-constants-aux (list)
  (cond ((equal (car list) 'quote)
	 list)
	(t
	 (append (list (car list))
		 (mapcar #'(lambda (one)
			     (cond ((listp one)
				    (quote-constants-aux one))
				   ((or (variablep one)
					(numberp one)
					(boundp one)) ; this seems odd - what if symbol is accidentally bound for some other purpose?
				    one)
				   (t
				    (list 'quote one))))
			 (cdr list))))))
			 
(defparameter pprint-state* nil)
(defparameter pat-trace* nil)
			 
(defun print-icarus-settings ()
  (unless pat-trace*
    (terpri)(princ "========= Current Icarus Setting =========")
    (terpri)(princ " Inference Engine: ")
    (print-setting inference* '(standard "Standard")
		   '(fast "Fast Matcher"))
    (terpri)(princ " Problem Solver: ")
    (print-setting problem-solver-enabled* '(meansends "ME ON") '(planner "PL ON") '(nil "OFF"))
    (when (equal problem-solver-enabled* 'meansends)
      (terpri)(princ " Skill Selection Heuristic: ")
      (print-setting skill-selection-heuristic* 
		     '(:MAX-EFFECTS-MATCHED "Maximize Matched Effects")
		     '(:MIN-UNSATISFIED-CONDITIONS "Minimize Unsatisfied Conditions")))
    (terpri)(princ "==========================================")))

(defun print-pat-memory-traces ()
  (let ((*print-right-margin* 78))
    (cond ((not (null ctrace*))
	   (terpri)(princ "----------")
	   (terpri)(princ "Cycle ")(princ cycle*)))
    (cond ((and (not (null gtrace*))
		(equal problem-solver-enabled* 'meansends))
	   (print-problems)))
    (cond ((or pat-trace*
	       (equal ptrace* 2))
	   (print-percepts T)) ; T = "raw" -- always use when pat-trace* is T
	  ((equal ptrace* 1)
	   (print-percepts)))
    (cond ((not (null btrace*))
	   (terpri) (princ "Beliefs:")
	   (pprint cstmh*)))
    nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;previously defined in macgyver.lisp

;simply commented out the use of extract-unchainable-conditions
(defun run-aux (n
		&key (timelimit 0) (mode nil))
  (check-essential-functions)

  ;; Compile a list of unchainable conditions for each skill
;  (if (< cycle* 2)
;      (extract-unchainable-conditions cltm* sltm*))

  (do ()
      ((or (and (numberp n) (> n 0) (>= cycle* n))
	   (and (> timelimit 0)
		(>= time* timelimit))
	   ;halt*
	   )
       (cond ((and (> timelimit 0)
		   (>= time* timelimit))
	      (print-timeout))
	     ((equal halt* 'noskill)
	      (print-no-skill))
	     ((equal halt* 'success)
	      (print-achieved))))
      (setq current-resources* nil)
      (setq learned-paths-used* nil)
      (sleep 0.1)
      (let ((starttime (get-internal-real-time))
	    percepts
	    agent-level-results)
	(setq pstm* (preattend))
	(setq percepts (copy-list pstm*))
	(cond ((equal inference* 'STANDARD) 
	       (setq cstm* nil)  ;; DGS DEBUG 12/30/11************
	       (setq cstm* (infer cltm* pstm* cstm*)))
	      ((equal inference* 'FAST)
	       (run-inference))
	      (t
	       (error "The parameter INFERENCE* is not set up properly!")))
	(setq astm* nil)
	;; update the belief heads (literals)
	(setf cstmh*
	      (mapcar #'cinstance-head cstm*))
	(cond ((= cycle* 1)
	       ;;Store the initial state
	       (push pstm* pstatetrace*)
	       (push cstm* cstatetrace*)
	       ;; flush history information from prior run if any
	       (setq prior-executing-intention* nil)
	       (setq problem-tree-history* nil)
	       ))
      ;If some action was taken in the previous cycle,
      ;store the modified state.
	;(cond ((not (null last-execution*))
	       ;(push pstm* pstatetrace*)
	       ;(push cstm* cstatetrace*)))
	;(setq last-execution* nil)
	(if pat-trace*
	    (print-pat-memory-traces)
	    (print-memory-traces))
	;;; REWRITE CODE FOLLOWS:
	(select-active-problem)
	(solve active-problem* executing-intention*)
	)
    ;;Episodic
    (register-env cstm*
		  (if executing-intention*
		      (if (intention-action-executed? executing-intention*)
			  executing-intention*)))
    (update-world)
    (when pprint-state*
      (pprint-state))
    (setq cycle* (1+ cycle*))))
