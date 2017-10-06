; POSTPROCESSOR.LISP
;  written as part of MacGyver project
;          by Dongkyu Choi

(defun post-process-elements-field (elements &optional (counter 1))
  (let ((first (car elements))
	(second (second elements))
	(third (third elements)))
    (cond ((null first) nil)
	  ;When the new syntax, (... is (...) ...) is used
	  ((and (equal second 'is) (listp third))
	   (let ((defined (car (member (car third) concepts*
				       :key #'head-name :test 'equal)))
		 completed)
	     ;if it is not a defined concept, i.e., a percept
	     (if (null defined)
	         ;if the identifying variable is already included
		 (if (equal first (second third))
		     (setq completed (list first second third))
	           ;if the identifying variable is missing
		   (setq
		    completed
		    (list first second
			  (append (list (car third) first) (cdr third)))))
	       ;if it is a defined concept
	       (progn (setq completed
			    (list first second
				  (generate-head-list-from-struct
				   defined
				   (find-bindings-to-complete-head
				    third defined counter))))
		      (incf counter)))
	     ;recursive call for the next one
	     (cons completed (post-process-elements-field
			      (cdddr elements) counter))))
	  ;When regular predicate is used
	  (t
	   (cons first
		 (post-process-elements-field (cdr elements) counter))))))


(defun attributep (sym-name)
 (cond ((atom sym-name)
	(cond ((numberp sym-name)
	       nil)
	      (t
	       (hat-attributep sym-name))))))

(defun hat-attributep (sym-name)
  (eq (elt (symbol-name sym-name) 0) #\^))

(defun separate-args-attrs (headlist)
  (let (arguments attributes flag)
    (do ((one (car headlist) (car headlist)))
	((or (null headlist) flag) (cons arguments attributes))
      (cond ((attributep one)
	     (setf attributes headlist)
	     (setf flag t))
	    (t
	     (setf arguments (append arguments (list one)))))
      (pop headlist))))

; FIND-BINDINGS-TO-COMPLETE-HEAD fills in missing arguments/attributes.
; The inputs are a list (incomplete) and a head structure (defined).
(defun find-bindings-to-complete-head (incomplete defined
				       &optional (counter-above 1))
  (when (equal (car incomplete) (head-name defined))
    (let* ((current (separate-args-attrs (cdr incomplete)))
	   (args (car current))
	   (attrs (cdr current))
	   (existing (separate-args-attrs (head-arguments defined)))
	   (defined-arg-names (car existing))
	   (defined-attr-names (cdr existing))
	   (defined-arg-values (subseq (head-values defined) 0 (length defined-arg-names)))
	   (defined-attr-values (subseq (head-values defined) (length defined-arg-names)))
	   (counter 1)
	   bindings)
      ;find bindings for args
      (do ((i 0 (1+ i)))
	  ((= i (length defined-arg-values)))
	(cond ((< i (length args))
	       (push (cons (nth i defined-arg-values) (nth i args)) bindings))
	      (t
	       (push (cons (nth i defined-arg-values)
			   (intern (concatenate
				    'string
				    "?GENVAR"
				    (princ-to-string counter-above)
				    "-"
				    (princ-to-string counter))))
		     bindings)
	       (incf counter))))
      ;find bindings for attrs
      (do ((i 0 (1+ i)))
	  ((= i (length defined-attr-names)))
	(let* ((field (nth i defined-attr-names))
	       (value (nth i defined-attr-values))
	       (temp (member field attrs :test 'equal)))
	  (cond (temp
		 (push (cons value (cadr temp)) bindings))
		(t
		 (push (cons value
			     (intern (concatenate
				      'string
				      "?GENVAR"
				      (princ-to-string counter-above)
				      "-"
				      (princ-to-string counter))))
		       bindings)
		 (incf counter)))))
      bindings)))

(defun generate-head-list-from-struct (head bindings)
  (let ((name (head-name head))
	(fields (head-arguments head))
	(vars (head-values head))
	values
	result)
    (setq result (list name))
    (setq values (subst-bindings bindings vars))
    (dotimes (i (length fields))
      (if (attributep (nth i fields))
	  (push (nth i fields) result))
      (push (nth i values) result))
    (reverse result)))

; SUBST-BINDING inputs a list of variable bindings, like ((?X . A)(?Y . B)),
; and a generic skill or action, like (STACK ?X ?Y), and substitutes the 
; bindings for variables to produce a specific result, like (STACK A B).  

(defun subst-bindings (bindings generic)
  (cond ((null bindings) generic)
	(t (subst-bindings (cdr bindings)
			   (subst (cdar bindings) (caar bindings) generic)))))

(defun extract-attributes (percept)
  (do ((i 2 (1+ i)))
      ((= i (length percept))
       (values percept nil))
    (if (and (symbolp (nth i percept))
	     (hat-attributep (nth i percept)))
	(return-from extract-attributes
	  (values (subseq percept 0 i) (subseq percept i))))))

(defun pmatches (pattern element bindings)
  (let (ptype etype pname eid)
    (cond ((and (equal (second pattern) 'is)
		(listp (third pattern)))
	   (setq ptype (car (third pattern)))
	   (setq pname (first pattern))
	   (setq pattern (third pattern)))
	  (t
	   (setq ptype (car pattern))
	   (setq pname (cadr pattern))))
    ;if element is a derived object in the form of a head structure
    (cond ((head-p element)
	   (setq eid (head-id element))
	   (setq etype (head-name element))
	   (setq element (subst-bindings (head-bindings element)
					 (head-listform element))))
	  (t
	   (setq etype (car element))))
;    (terpri)(princ "ptype: ")(princ ptype)
;    (terpri)(princ "pname: ")(princ pname)
;    (terpri)(princ "pattern: ")(princ pattern)
;    (terpri)(princ "etype: ")(princ etype)
;    (terpri)(princ "eid: ")(princ eid)
;    (terpri)(princ "element: ")(princ element)
    ;if the names match
    (let (flag regular-attributes hatted-attributes)
      (multiple-value-setq (regular-attributes hatted-attributes)
	(extract-attributes element))
      (if (null hatted-attributes)
	  (multiple-value-setq (flag bindings)
	    (match-standard-percept pattern element bindings))
	(multiple-value-setq (flag bindings)
	  (match-hatted-percept
	   pattern regular-attributes hatted-attributes bindings)))
;      (terpri)(princ "flag: ")(princ flag)
      (let ((nbind (assoc pname bindings)))
	;if the pattern name already exists in the bindings
	(if nbind
	    ;if the existing binding is not equal to eid
	    ;and eid is not null
	    (if (and eid (not (equal (cdr nbind) eid)))
		(setq flag nil))
	  ;if the pattern name does not exist in the bindings
	  ;if the pattern name is a variable
	  (if (variablep pname)
	      ;push binding if eid is not null
	      (if eid
		  (push (cons pname eid) bindings))
	    ;if the pattern name is a constant
	    ;if the pattern name is not equal to eid
	    (if (and eid
		     (not (equal pname eid)))
		(setq flag nil)))))
      (if flag
	  (cons flag bindings)
	(cons nil bindings)))))

(defun match-standard-percept (pattern element bindings)
  ;Return with the null flag if the types are different
  (unless (equal (car pattern) (car element))
    (return-from match-standard-percept
      (values nil bindings)))
  (let ((flag t))
    ;Match names
    (cond ((variablep (cadr pattern))
	   (multiple-value-setq (flag bindings)
	     (check-existing-binding-and-add-if-not
	      (cadr pattern) (cadr element) bindings))
	   (if (null flag)
	       (return-from match-standard-percept (values nil bindings))))
	  (t
	   (unless (and (cadr pattern) (equal (cadr pattern) (cadr element)))
	     (return-from match-standard-percept (values nil bindings)))))
    ;Match attribute-value pairs
    (do ((i 2 (1+ i)))
	((>= i (length pattern))
	 (values flag bindings))
      (let ((pattern-attribute (nth i pattern))
	    variable match value)
	(incf i)
	(setq variable (nth i pattern))
	(setq match (member pattern-attribute element :test 'equal))
	(setq value (cadr match))
	(cond ((variablep variable)
	       (multiple-value-setq (flag bindings)
		 (check-existing-binding-and-add-if-not
		  variable value bindings))
	       (if (null flag)
		   (return-from match-standard-percept (values nil bindings))))
	      (t
	       (unless (and variable (equal variable value))
		 (return-from match-standard-percept (values nil bindings)))))))))

(defun check-existing-binding-and-add-if-not (variable value bindings)
  (let ((existing (assoc variable bindings)))
    (cond ((null existing)
	   (push (cons variable value) bindings)
	   (values t bindings))
	  ((equal value (cdr existing))
	   (values t bindings))
	  (t
	   (values nil bindings)))))

(defun match-hatted-percept (pattern regular hatted-attributes bindings)
  ;Return with the null flag if the types are different
  (unless (equal (car pattern) (car regular))
    (return-from match-hatted-percept
      (values nil bindings)))
  (let ((flag t))
    ;Match names and arguments
    (do ((i 1 (1+ i)))
	((= i (length regular)))
      (let ((variable (nth i pattern))
	    (value (nth i regular)))
	(cond ((variablep variable)
	       (multiple-value-setq (flag bindings)
		 (check-existing-binding-and-add-if-not
		  variable value bindings))
	       (if (null flag)
		   (return-from match-hatted-percept (values nil bindings))))
	      (t
	       (unless (and variable (equal variable value))
		 (return-from match-hatted-percept (values nil bindings)))))))
    ;Match attribute-value pairs
    (do ((i (length regular) (1+ i)))
	((>= i (length pattern))
	 (values flag bindings))
      (let ((pattern-attribute (nth i pattern))
	    variable match value)
	(incf i)
	(setq variable (nth i pattern))
	(setq match (member pattern-attribute hatted-attributes :test 'equal))
	(setq value (cadr match))
	(cond ((variablep variable)
	       (multiple-value-setq (flag bindings)
		 (check-existing-binding-and-add-if-not
		  variable value bindings))
	       (if (null flag)
		   (return-from match-hatted-percept (values nil bindings))))
	      (t
	       (unless (and variable (equal variable value))
		 (return-from match-hatted-percept (values nil bindings)))))))))

#|
;Example 0: FULL LIST
(post-process-elements-field '(?o1 is (block ?o1 ^left ?l1 ^right ?r1 ^bottom ?b1 ^top ?t1)
	    ?o2 is (block ?o2 ^left ?l2 ^right ?r2 ^bottom ?b2 ^top ?t2)))

;1) Real objects in 'elements' field
    ;Example 1:
    (post-process-elements-field '(?o1 is (block ^left ?l1 ^right ?r1 ^bottom ?b1 ^top ?t1)
		?o2 is (block ^left ?l2 ^right ?r2 ^bottom ?b2 ^top ?t2)))
    ;Example 2:
    (post-process-elements-field '(?o1 is (block ^left ?l1 ^right ?r1 ^bottom ?b1)
		?o2 is (block ^left ?l2 ^right ?r2 ^top ?t2)))
    ;Example 3:
    (post-process-elements-field '(?o1 is (block ^left ?l1 ^right ?r1)
		?o2 is (block ^left ?l2 ^right ?r2)))

;2) A virtual object in 'elements' field
    ;Example 1:
    (post-process-elements-field '(?o1 is (block ?o1 ^left ?l1 ^right ?r1 ^bottom ?b1 ^top ?t1)
		?o2 is (tower ?o3 ^left ?l2 ^right ?r2 ^bottom ?b2 ^top ?t2)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Still working on below mentioned examples

;3) Skills
    ;Example 1:
    (post-process-elements-field '(?g is (gripper)
		?o1 is (block)
		?o2 is (block)))
    ;Example 2:
    (post-process-elements-field '(?g is (gripper ^x ?gx ^y ?gy)
		?o1 is (block ^left ?l1 ^right ?r1 ^bottom ?b1 ^top ?t1)
		?o2 is (block ^left ?l2 ^right ?r2 ^bottom ?b2 ^top ?t2)))
    ;Example 3:
    (post-process-elements-field '(?g is (gripper ^x ?gx ^y ?gy)
		?o is (block ^left ?l ^right ?r ^bottom ?b ^top ?t)))
|#
