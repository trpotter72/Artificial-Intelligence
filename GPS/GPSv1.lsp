;;General Problem Solver Version 1
;;By Trenton Potter
;;From Paradigms of Artificial Intelligence Programming by Peter Norvig

;Description
;;Solves problems given an initial state, goal state, and list of operators which modify states given preconditions


;Issues with program
;;Does not check to see if goals are still achieved after initial check (clobbering siblings problem)
;;Looping is not checked for
;;Because of Depth first execution interleaving, can go down an unsolvable & unreturnable path
;;

;;Variable declarations
(defvar *state* nil "Current state (list of conditions)")

(defvar *ops* nil "List of available operators.")

;;Defines operator structure
(defstruct op "Structure of an operator"
	(action nil) (preconditions nil) (add-list nil) (delete-list nil))


;;GPS function and helper functions	
(defun GPS (*state* goals *ops*)
	"Achieve all goals using given operators from current state"
	(if (every #'achieve goals) ;execute achieve on all goals
		'solved))				;return solved if all achieve calls return true
		
(defun achieve (goal)
	"A goal is achieved if it is already present or if it can be achieved via an applicable op"
	(or (member goal *state*)
		(some #'apply-op 
			(find-all goal *ops* :test #'appropriate-p))))
			
(defun find-all (item sequence &rest keyword-args &key (test #'eql) test-not &allow-other-keys)
	"Find all elements of a sequence that match an item, according to the keywords.  Doesn't alter the sequence"
	(if test-not
		(apply #'remove item sequence :test-not (complement test-not) keyword-args)
		(apply #'remove item sequence :test (complement test) keyword-args)))
		
(defun appropriate-p (goal op)
	"An op is appropriate to a goal if it is in its add list"
	(member goal (op-add-list op)))
	
(defun apply-op (op)
	"Print a message and update *state* if op is applicable."
	(when (every #'achieve (op-preconditions op))
		(print (list 'executing (op-action op)))
		(setf *state* (set-difference *state* (op-delete-list op)))
		(setf *state* (union *state* (op-add-list op)))
		t))

;;Creates a small number of operators and a current state		
(defun init-test ()
	(setf *state* '(at-home have-car))
	(setf *ops* 
		(list 
			(make-op :action 'drive-to-work
				:preconditions '(at-home have-car)
				:add-list '(at-work)
				:delete-list '(at-home)) 
			(make-op :action 'work
				:preconditions '(at-work)
				:add-list '(have-money tired)
				:delete-list '())
			(make-op :action 'drive-to-home
				:preconditions '(at-work have-car)
				:add-list '(at-home)
				:delete-list '(at-work))))) 
