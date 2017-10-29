;;****************************************************************************
;; COMPILER.LISP
;;  for ICARUS 2017
;;  written by Dongkyu Choi
;;****************************************************************************

;; FUNCTION LIST:
;;
;; CREATE-CONCEPTS
;;   |- CREATE-CONCEPT
;;        |- GET-POS-CONDS
;;             |- GET-POS-CONDS
;;        |- GET-NEG-CONDS
;;             |- GET-NEG-CONDS
;;        |- MAKE-CONCEPT
;;        |- PRINT-ERROR
;;
;; CREATE-SKILLS
;;   |- CREATE-SKILL-CLAUSE
;;        |- MAKE-SCLAUSE
;;        |- QUOTE-CONSTANTS
;;        |- PRINT-ERROR

;;****************************************************************************
;; Concept Compiler
;;****************************************************************************
(defmacro create-concepts (&rest concepts)
  `(let ((concepts (quote ,concepts))
	 (is-null-result nil))
     (do ((next-concept (car concepts) (car concepts)))
	 ;;exit condition
	 ((or (null concepts) is-null-result)
	  (cond (is-null-result
		 (error (format nil "ICARUS: Concept creation failed for ~A!~%"
				is-null-result)))
		(t
		 (post-process-concepts))))
       ;;do body
       (let ((result (create-concept next-concept)))
	 (if (null result)
	     (setf is-null-result (caar next-concept))
	     (progn
	       (setf is-null-result nil)
	       (push result cltm*)
	       )))
       (pop concepts))))

(defun post-process-concepts ()
  (setq cltm* (reverse cltm*))

  ;; TO DO: sort by dependency
  (loop while (not (null cltm*))
     with sorted_list = (list)
     do(prog* (
               (candidate (pop cltm*))
               (ready-to-add t)
               (dependencies (get-dependencies candidate)))
              (loop for dependency in dependencies
                 do(if (member-if (lambda (x) (eq dependency (concept-head x)
                                                dependency cltm*)) cltm*)
                       (setq ready-to-add nil))
                finally (append (if ready-to-add sorted_list cltm*) (list candidate))))
    finally (setq cltm* sorted_list)))

(defun get-dependencies (concept)
  "Given a concept definition, return the names of concepts it depends upon"
  (loop for element in (concept-elements concept)
    collect (if (eq (car element) 'not)
                (caadr element)
                (car element))))




(defun create-concept (concept)
  (let ((head (car concept))
	(body (cdr concept)))
    (setq head (process-concept-head head))
    (let (id
	  elements
	  tests
	  binds)
      (do ((next-field (car body) (car body))
	   (next-spec (cadr body) (cadr body)))
	  ((null body)
	   (setq id (gensym "CNCPT"))
	   (make-concept :id id
			 :head head
			 :elements elements
			 :tests tests
			 :binds binds))
	(cond ((or (eq next-field ':percepts)
		   (eq next-field ':conditions)
		   (eq next-field ':relations)
		   (eq next-field ':elements))
	       (unless (eq next-field ':elements)
		 (print-warning next-field "field" "a concept"))
	       (setq elements
		     (append elements
			     (mapcar #'process-concept-head next-spec))))
	      ((eq next-field ':tests)
	       (setq tests next-spec))
	      ((or (eq next-field ':binds)
		   (eq next-field ':attributes))
	       (unless (eq next-field ':binds)
		 (print-warning next-field "field" "a concept"))
	       (setq binds (append binds (process-binds next-spec))))
	      (t (print-error next-field "field" "a concept")))
	(setq body (cddr body))))))

(defun process-concept-head (head)
  (let ((name (car head))
	(rest (cdr head)))
    (cond
     ;;if negated head
     ((equal name 'not)
      (list 'not (process-concept-head (car rest))))
     ;;if ^id attribute is used
     ((equal (car rest) '^id)
      head)
     (t
      (let (id attrval flag)
	(do ((i 0 (1+ i)))
	    ((or (= i (length rest)) flag)
	     (if flag
		 ;;if a hat attribute other than ^id was found
		 (append (list name '^id id) attrval)
	       ;;if reached the end
	       (if (= (length rest) 1)
		   (list name '^id (car rest))
		 (list name '^id rest))))
	  (cond
	   ;;if ^id is found at a wrong place in the head
	   ((equal '^id (nth i rest))
	    (error
	     "Attribute ^id can only come right after the concept name!"))
	   ;;if a hat attribute is found (other than ^id)
	   ((attributep (nth i rest))
	    (setq id (subseq rest 0 i))
	    (setq attrval (subseq rest i))
	    (setq flag t)))))))))

(defun attributep (sym-name)
 (cond ((atom sym-name)
	(cond ((numberp sym-name)
	       nil)
	      (t
	       (hat-attributep sym-name))))))

(defun hat-attributep (sym-name)
  (eq (elt (symbol-name sym-name) 0) #\^))

(defun variablep (sym-name)
 (cond ((atom sym-name)
	(cond ((numberp sym-name)
	       nil)
	      (t
	       (eq (elt (symbol-name sym-name) 0) #\?))))))

(defun process-binds (binds)
  (cond ((null binds) nil)
	((variablep (car binds))
	 (cons (list (car binds) (cadr binds))
	       (process-binds (cddr binds))))
	((and (listp (car binds))
	      (variablep (caar binds)))
	 (cons (car binds)
	       (process-binds (cdr binds))))
	(t
	 (print-error (car binds) "variable" ":BINDS field")
	 nil)))

;; This function is also called by create-skill-clause in solver-rewrite.lisp
(defun print-error (next x y)
  (error (format nil "ICARUS: ~A is not a valid ~A for ~A.~%" next x y)))

(defun print-warning (next x y)
  (warn (format nil "~A is a deprecated ~A for ~A." next x y)))

;;****************************************************************************
;; Skill Compiler
;;****************************************************************************
(defmacro create-skills (&rest skills)
  `(let ((skills (quote ,skills))
	 result)
     (do ((next-skill (car skills) (car skills)))
	 ((null skills)
	  (setq sltm* (append sltm* (reverse result)))
	  ;;(post-process-skills)
	  nil)
       (push (create-skill next-skill) result)
       (pop skills))))

(defun post-process-skills ()
  )

(defun create-skill (skill)
  (let ((head (car skill))
	(body (cdr skill))
	id
	elements
	tests
	actions
	subskills
	changes
	effects)
    (do ((next-field (car body) (car body))
	 (next-spec (cadr body) (cadr body)))
	((null body)
	 (setq id (gensym "SKILL"))
	 (make-skill :id id
		     :head head
		     :elements elements
		     :tests tests
		     :actions actions
		     :subskills subskills
		     :changes changes
		     :effects effects))
      (cond ((or (eq next-field ':percepts)
		 (eq next-field ':conditions)
		 (eq next-field ':elements))
	     (unless (eq next-field ':elements)
	       (print-warning next-field "field" "a skill"))
	     (setq elements
		   (append elements
			   (mapcar #'process-concept-head next-spec))))
	    ((eq next-field ':tests)
	     (setq tests next-spec))
	    ((eq next-field ':actions)
	     (setq actions next-spec))
	    ((eq next-field ':subskills)
	     (setq subskills next-spec))
	    ((eq next-field ':changes)
	     (setq effects
		   (mapcar #'process-concept-head next-spec)))
	    ((eq next-field ':effects)
	     (setq effects
		   (mapcar #'process-concept-head next-spec)))
	    (t (print-error next-field "field" "a skill")))
      (setq body (cddr body)))))

;;****************************************************************************
;; End of COMPILER.LISP
;;****************************************************************************
