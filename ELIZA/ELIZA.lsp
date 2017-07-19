;;ELIZA dialogue pattern matching program
;;Reproduced by Trenton Potter
;;From Peter Norvig's Paradigms of Artificial Intelligence Programming


;;;Constants;;;
(defconstant fail nil "Indicates pat-match failure")

(defconstant no-bindings '((t . t)) "Pat-match success with no variables")

;;;Functions;;;

;;Auxillary Functions
(defun simple-equal (x y)
	"Are x and y equal? (Doesn't check inside the strings.)"
	(if (or (atom x) (atom y))
		(eql x y)
		(and (simple-equal (first x) (first y))
			 (simple-equal (rest x) (rest y)))))
			 
 (defun starts-with (list x)
	"Is this a list AND is the list's first element x?"
	(and (consp list) (equal x (first list))))
	
(defun variable-p (x)
	"Is x a variable? (a symbol beginning with '?')"
	(and (symbolp x) (equal (char (symbol-name x) 0) #\?)))
				
(defun segment-pattern-p (pattern)
	"Is this a segment matching pattern: ((?* var) . pat)"
	(and 	(consp pattern)
			(starts-with (first pattern) '?*)))	

			
;;Primary Functions	 
(defun pat-match (pattern input &optional (bindings no-bindings))
	"Match pattern against input in the context of bindings"
	(cond 	((eq bindings fail) fail)	;If given failed binding list, pass on fail
			((variable-p pattern)		
				(match-variable pattern input bindings)) ;If pattern is a var pass attempt to extend binding / verify it holds
			((eql pattern input) bindings)				;If the pattern and input match, end checking and return bindings
			((segment-pattern-p pattern)
				(segment-match pattern input bindings))
			((and (consp pattern) (consp input))
				(pat-match (rest pattern) (rest input) 
					(pat-match (first pattern) (first input) bindings))) ;If pattern and input are both lists, continue checking for more variables (already established they do not match)
			(t fail))) 
	
(defun match-variable (var input bindings)
	"Does VAR match input? Uses or updates and returns bindings"
	(let ((binding (get-binding var bindings)))
		(cond 	((not binding) (extend-bindings var input bindings))
				((equal input (binding-val binding)) bindings)
				(t fail))))

(defun segment-match (pattern input bindings &optional (start 0))
	"Match the segment pattern ((?* var) . pat) against input."
	(let (	(var (second (first pattern)))
			(pat (rest pattern)))
		(if (null pat)
			(match-variable var input bindings)
			;;Assumes pat starts with a constant
			;;(doesnt have two consecutive variables
			(let ((pos (position (first pat) input
										:start start :test #'equal)))
				(if (null pos)
					fail
					(let ((b2 (pat-match pat (subseq input pos) (match-variable var (subseq input 0 pos)bindings))))
						;;if this match fails, tries a longer one within the remaining input
						;;If it works, check that the variables match
						(if (eq b2 fail)
							(segment-match pattern input bindings (+ pos 1))
							 b2)))))))
							 
(defun get-binding (var bindings)
	"Find a (variable . value) pair in a binding list."
	(assoc var bindings))
	
(defun binding-val (binding)
	"Get the value part of a single binding"
	(cdr binding))

(defun lookup (var bindings)
	"Get the value part (for var) from a bindings list"
	(binding-val (get-binding var bindings)))
	
(defun extend-bindings (var val bindings)
	"Add a (variable . value) pair to a bindings list"
	(cons (cons var val) 
		(if (eq bindings no-bindings) nil
			bindings)))