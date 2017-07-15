(defparameter *simplegrammar*
'(	(sentence -> (noun-phrase verb-phrase))
	(noun-phrase -> (Article Noun)(Article Adjective Noun))
	(verb-phrase -> (Verb noun-phrase))
	(Article -> the a)
	(Noun -> man ball table snake fox)
	(Verb -> hit took saw liked)
	(Adjective -> fat small large skinny))
"A simple grammar for an english sentence")

(defvar *grammar* *simplegrammar*)

(defun random-elt (choices)
	"Returns a random element from a list as a list"
	(list (elt choices (random (length choices)))))

(defun mappend (fn values)
	"Calls append on the values returned by mapcar"
	(apply #'append (mapcar fn values)))
	
(defun rule-lhs (rule)
	"Returns the LHS of a rule"
	(first rule))
	
(defun rule-rhs (rule)
	"Returns the RHS of a rule"
	(rest (rest rule)))
	
(defun rewrites (category)
	"Returns a list of the possible rewrites for a category"
	(rule-rhs (assoc category *grammar*)))
	
(defun generate (phrase)
	"Generate a random sentence or phrase from a rule"
	(let ((choices (rewrites phrase)))
		(cond	( (listp phrase)
				  (mappend #'generate phrase))
				( choices
				  (generate (random-elt choices)))
				(  t
				  (list phrase)))))