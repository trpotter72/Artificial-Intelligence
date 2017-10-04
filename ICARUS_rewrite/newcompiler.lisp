; NEWCOMPILER.LISP
;  written as part of MacGyver project
;          by Dongkyu Choi

; ORIGINAL FUNCTION HIERARCHY FOR THE COMPILER:
; (* denotes a lowest-level function.)
;
; CREATE-CONCEPTS (HOLDOVER.LISP)
;   |- CREATE-CONCEPT
;        |- GET-POS-CONDS
;             |- GET-POS-CONDS
;        |- GET-NEG-CONDS
;             |- GET-NEG-CONDS
;        |- MAKE-CONCEPT
;        |- PRINT-ERROR
; 
; CREATE-SKILLS (SOLVER-REWRITE.LISP)
;   |- CREATE-SKILL-CLAUSE
;        |- MAKE-SCLAUSE
;        |- QUOTE-CONSTANTS
;        |- PRINT-ERROR

; NEW ICARUS SYNTAX:
;
;   Concepts:
;     (<head>
;      :elements   (<var> is <obj>
;                   ...)
;      :conditions (<predicate> ...)
;      :tests      (<LISP function> ...)
;      :attributes (<var> is <LISP function>
;                   <var> is <LISP function>
;                   ...)
;     )
;     where <head> is:
;       (<name> <var> ... ^attr <var> ...)
;
;   Skills:
;     (<head>
;      :elements   (<var> is <obj>
;                   ...)
;      :conditions (<predicate> ...)
;      :actions    (<LISP function> ...)
;      :subskills  (<head> ...)
;      :effects    (<predicate>
;                   <var> is <obj>
;                   ...)
;     )
;     where <head> is a predicate

;****************************************************************************
; ICARUS Memories and Other Global Variables
;****************************************************************************
(defvar cltm* nil)
(defvar sltm* nil)
(defvar gstm* nil)

(defvar concepts* nil)
(defvar primitive-concepts* nil)
(defvar id-count* 0)

;****************************************************************************
; Initialization Functions
;****************************************************************************
(defun clear-concepts ()
  (setq cltm* nil))

(defun remove-concepts ()
  (setq cltm* nil))

(defun rc ()
  (remove-concepts))

(defun clear-skills ()
  (setq sltm* nil))

(defun remove-skills ()
  (setq sltm* nil))

(defun rs ()
  (remove-skills))

(defun clear-goals ()
  (setq gstm* nil))

(defun remove-goals ()
  (setq gstm* nil))

(defun rg ()
  (remove-goals))

(defun clear ()
  (clear-concepts)
  (if (equal inference* 'fast) (clear-fast-matcher))
  (clear-skills)
  (clear-goals)
  (setq id-count* 0)
  t)

;****************************************************************************
; Structural Definitions and their Support Functions
;****************************************************************************
; The two fields pos-dependencies neg-dependencies were added by Son To for fast deductive closure computation. 
;pivot marks the variable(s) used for partial matching.
(defstruct concept
  head id elements conditions positives negatives tests
  pos-dependencies neg-dependencies
  attributes
  ;pivot threshold
  ;value duration expected pschildren ngchildren siblings
  ;instances rmdup attributes calculates counters
  )

(defstruct cinstance
  head id bindings subgoals 
  (degmatch 1.0) (timestamp cycle*) pos-dependencies
  neg-dependencies percepts total-percepts probability
  (time-stamps (cons nil 'NOW)) derived-object)

(defstruct sclause
  head				
  id 
  elements
  tests
  conditions
  effects
  subskills
  actions
  )

;Note that 'values' of 'arguments' can be represented with variables
(defstruct head id name listform arguments values bindings)

;Heads are compatible when the name and the arguments are identical.
;It does not matter what variables or values are used for those arguments,
;which are listed under head-values. Furthermore, the bindings don't matter.
(defun compatible-heads (head1 head2)
  (and (equal (head-name head1) (head-name head2))
       (equal (head-arguments head1) (head-arguments head2))))

(defun same-instantiated-head (head1 head2)
  (and (compatible-heads head1 head2)
       (equal (subst-bindings (head-bindings head1) (head-values head1))
	      (subst-bindings (head-bindings head2) (head-values head2)))))

(defun process-new-arguments (arguments)
  (let (fields values (counter 1))
    (do ((argument (car arguments) (car arguments)))
	((null arguments)
	 (cons (reverse fields) (reverse values)))
      (cond
       ;If the argument starts with ^, it is an attribute name and
       ;what follows is its value.
       ((attributep argument)
	(push argument fields)
	(pop arguments)
	(push (pop arguments) values))
       ;If not, it is an actual argument, it needs a name (ARG#).
       (t
	(push (intern (concatenate 'string "ARG" (princ-to-string counter)))
	      fields)
	(incf counter)
	(push argument values)(pop arguments))))))

(defun same-cinstance (cinst1 cinst2)
  (same-instantiated-head (cinstance-head cinst1) (cinstance-head cinst2)))

(defun cinstance-name (cinstance)
  (head-name (cinstance-head cinstance)))

(defun cinstance-args (cinstance)
  (let ((head (cinstance-head cinstance)))
    (subst-bindings (head-bindings head) (head-values head))))

(defun cinstance-args-with-attributes (cinstance)
  (let ((head (cinstance-head cinstance)))
    (subst-bindings (head-bindings head) (cdr (head-listform head)))))

(defun concept-name (concept)
  (head-name (concept-head concept)))

;Time stamps are not compatible with the McGyver changes. Disabling...
(defun time-stamped (head)
  nil)

;****************************************************************************
; Concept Compiler
;****************************************************************************
(defmacro create-concepts (&rest concepts)
  `(let ((concepts (quote ,concepts))
	 (is-null-result nil))
     (do* ((next-concept (car concepts) (car concepts)))
	  ;exit condition
	  ((or (null concepts) is-null-result)
	   (if is-null-result
	       nil			; exit w/o reversing cltm*
	     (progn
	       (setq cltm* (reverse cltm*))
	       nil))
	   (post-process-concepts))
	  ;do body
	  (let ((result (create-concept next-concept)))
	    (if (null result)
		(setf is-null-result t)
	      (progn
		(setf is-null-result nil)
		(push result cltm*))))
	  (pop concepts))))

(defun post-process-concepts ()
  (dolist (concept cltm*)
    (setf (concept-elements concept)
	  (post-process-elements-field (concept-elements concept)))))

(defun create-concept (concept)
  (let ((defined (car (member (caar concept) concepts*
			      :key #'head-name :test 'equal)))
	head
	(processed-args (process-new-arguments (cdar concept))))
    ;Create new head
    (setq head
	  (make-head :name (caar concept)
		     :listform (car concept)
		     :arguments (car processed-args)
		     :values (cdr processed-args)))
    ;Make sure the head is the same as those of existing concepts with the same name
    (cond ((and defined
		(not (compatible-heads head defined)))
	   (terpri)
	   (princ "The concept head does not match with already defined ones.")
	   (terpri)(princ "Please use the same arguments for the head.")
	   (return-from create-concept nil))
	  ((null defined)
	   (push head concepts*)))
    ;Create the new concept
    (let (id
	  elements
	  positives
	  negatives
	  conditions
	  tests
	  attributes)
      (setq concept (cdr concept))
      (do ((next-field (car concept) (car concept))
	   (next-spec (cadr concept) (cadr concept)))
	  ((null concept)
	   (cond ((and (null positives) (null negatives)
		       (not (member (head-name head) primitive-concepts*)))
		  (push (head-name head) primitive-concepts*)))
	   (setq id (gensym "CNPT"))
	   (setf (head-id head) id)
	   (make-concept :id id
			 :attributes attributes
			 :head head :elements elements :conditions conditions
			 :positives positives :negatives negatives
			 :tests tests))
	(cond ((or (eq next-field ':elements)
		   (eq next-field ':percepts))
	       (setq elements next-spec))
	      ((or (eq next-field ':conditions)
		   (eq next-field ':relations))
	       (setq conditions next-spec)
	       (setq positives (get-pos-conds next-spec))
	       (setq negatives (get-neg-conds next-spec)))
	      ((eq next-field ':tests)(setq tests next-spec))
	      ((eq next-field ':attributes)
	       (setq attributes (process-attributes next-spec)))
	      (t (print-error next-field "field" "concept")))
	(setq concept (cddr concept))))))

(defun process-attributes (attributes)
  (let ((first (car attributes))
	(second (cadr attributes))
	(third (caddr attributes)))
    (cond ((null attributes) nil)
	  ((equal second 'is)
	   (cons (list first second third)
		 (process-attributes (cdddr attributes))))
	  (t
	   (cons first (process-attributes (cdr attributes)))))))

(defun get-pos-conds (conditions)
  (cond ((null conditions) nil)
	((not (eq (caar conditions) 'not))
	 (cons (car conditions) (get-pos-conds (cdr conditions))))
	(t (get-pos-conds (cdr conditions)))))

(defun get-neg-conds (conditions)
  (cond ((null conditions) nil)
	((eq (caar conditions) 'not)
	 (cons (cadar conditions) (get-neg-conds (cdr conditions))))
	(t (get-neg-conds (cdr conditions)))))

;; This function is also called by create-skill-clause in solver-rewrite.lisp
(defun print-error (next x y)
  (terpri)(princ "Syntax error: ")
  (princ next)(princ " is not a valid ")
  (princ x)(princ " for an Icarus ")
  (princ y)(princ ".") nil)

;****************************************************************************
; Skill Compiler
;****************************************************************************
(defmacro create-skills (&rest skills)
  `(let ((skills (quote ,skills))
	 result)
     (do ((next-skill (car skills) (car skills)))
	 ((null skills)
	  (setq sltm* (append sltm* (reverse result)))
	  (post-process-skills)
	  nil)
       (push (create-skill-clause next-skill) result)
       (pop skills))))

(defun post-process-skills ()
  (dolist (skill sltm*)
    (setf (sclause-elements skill)
	  (post-process-elements-field (sclause-elements skill)))
    (setf (sclause-effects skill)
	  (post-process-elements-field (sclause-effects skill)))))

(defun create-skill-clause (skill)
  (let ((head (car skill))
	(id nil)
	(elements nil)
	(tests nil)
	(conditions nil)
	(effects nil)
	(subskills nil)
	(actions nil))
    (pop skill)				; get rid of head, rest is alternating :key <spec> pairs
    (do ((next-field (car skill) (car skill))
	 (next-spec (cadr skill) (cadr skill)))
	((null skill)
	 (cond ((null id) (setq id (incf id-count*))))
	 (make-sclause :head head
		       :id id
		       :elements elements
		       :tests tests
		       :conditions conditions
		       :effects effects
		       :subskills subskills
		       :actions actions))
; (quote-constants actions))) ; check out / find out what this does 
      ;; do keywords need to be quoted below?
      (cond ((or (eq next-field ':elements)
		 (eq next-field ':percepts))
	     (setq elements next-spec))
	    ((eq next-field ':id)(setq id next-spec))
	    ((eq next-field ':tests)(setq tests next-spec))
	    ((eq next-field ':conditions)(setq conditions next-spec))
	    ((eq next-field ':effects)(setq effects next-spec))
	    ((eq next-field ':subskills)(setq subskills next-spec))
	    ((eq next-field ':actions)(setq actions next-spec))
	    (t (print-error next-field "field" "skill")))
      (setq skill (cddr skill)))))

;TEST CASES
#|
((tower ?o1 ?o2 ^left ?l ^right ?r ^bottom ?b ^top ?t)
 :elements   (?o1 is (block ^left ?l1 ^right ?r1 ^bottom ?b1 ^top ?t1)
              ?o2 is (block ^left ?l2 ^right ?r2 ^bottom ?b2 ^top ?t2))
 :conditions ((on ?o1 ?o2))
 :attributes (?l is (min ?l1 ?l2) ?r is (max ?r1 ?r2)
	      ?b is (min ?b1 ?b2) ?t is (max ?t1 ?t2))
)

((tower ?o1 ?o2 ^left ?l ^right ?r ^bottom ?b ^top ?t)
 :elements   (?o1 is (block ^left ?l1 ^right ?r1 ^bottom ?b1 ^top ?t1)
              ?o2 is (tower ?o3 ^left ?l2 ^right ?r2 ^bottom ?b2 ^top ?t2))
 :conditions ((on ?o1 ?o3))
 :attributes (?l is (min ?l1 ?l2) ?r is (max ?r1 ?r2)
	      ?b is (min ?b1 ?b2) ?t is (max ?t1 ?t2))
)

((on ?o1 ?o2) 
 :elements (?o1 is (block ^left ?l1 ^right ?r1 ^bottom ?b1)
            ?o2 is (block ^left ?l2 ^right ?r2 ^top ?t2))
 :tests    ((*near-equal ?b1 ?t2)
            (*overlapping ?l1 ?r1 ?l2 ?r2))
)

((stack ?g ?o1 ?o2)
 :elements   (?g is (gripper)
              ?o1 is (block)
              ?o2 is (block))
 :conditions ((holding ?g ?o1) (not (on ?other ?o2)))
 :subskills  ((move-over ?g ?o2)
              (lower-onto ?g ?o1 ?o2)
	      (ungrasp ?g ?o1))
 :effects    ((on ?o1 ?o2) (not (holding ?g ?o1))) 
)

((lower-onto ?g ?o1 ?o2)
 :elements   (?g is (gripper ^x ?gx ^y ?gy)
              ?o1 is (block ^left ?l1 ^right ?r1 ^bottom ?b1 ^top ?t1)
              ?o2 is (block ^left ?l2 ^right ?r2 ^bottom ?b2 ^top ?t2))
 :conditions ((holding ?g ?o1)
              (directly-above ?o1 ?o2)
              (not (on ?other ?o2)))
 :subskills  ((lower-block ?g ?o1 ^rate 1))
 :effects    ((on ?o1 ?o2)
              ?o1 is (block ^bottom ?t2 ^top (+ ?t2 (- ?t1 ?b1)))
              ?g is (gripper ^y (- ?gx (- ?b1 ?t2))))
)

((lower-block ?g ?o ^rate ?r)
 :elements   (?g is (gripper ^x ?gx ^y ?gy)
              ?o is (block ^left ?l ^right ?r ^bottom ?b ^top ?t))
 :conditions ((holding ?g ?o))
 :actions    ((*lower ?g r))
 :effects    (?g is (gripper ^y (- ?gx ?r))
              ?o is (block ^bottom (- ?b ?r) ^top (- ?t ?r)))
)

|#
