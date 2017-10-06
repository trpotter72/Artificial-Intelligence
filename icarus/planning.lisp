;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Written by Son To, September-2013
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;  PLANNING: HIERARCHICAL FORWARD SEARCH ALGORITHM
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Load from "C:/users/to thanh son/dropbox/Icarus-num"

;;Function get-start-node builds the start node of the search space. 
;;A node is a structure of the form (:state :htask :previous-node :heuristic), where htask is a hiararchical task 
;;representing an instantiated skill leading from the previous state (node) to the current state.
;;The values of the htask and previous-node of the start-node are nil.
;;Initialize the open-queue, the heuristic-based-sorted queue of unexpanded nodes, with the start node. 
;;The nodes in the open-queue are sorted in the order of their heuristic values, e.g., 
;;the number of goals unsatisfied in their states (goal heuristic search).
;;The best unexpanded node is the first node in the open queue. 
;;The detected plan is extracted to the variable hplan* which is a list of htasks. 

;;Search node in the search tree. A node consists of a belief state, a previous node, 
;;a htask leading to the node from the previous node, and a heuristic, the number of unsatisfied goals.
(defstruct node state htask previous heuristic)

;;The structure cconcept is a variation of concept used for planning purpose only. 
;;Conditions (positives and negatives) contains only predicates while elements contains objects, i.e., the predicates indicating them and their IDs.
;;Each of attributes is a pair/list of the form (attr f), where f is a formula evaluated to be either a number or
;;nil if some variable in f is unbound to a number.

(defstruct cconcept name arguments elements
  positives negatives tests attributes
  pos-dependencies neg-dependencies)

;;The skill structure is a variation of sclause used for planning purpose only.
;;The skill-id is the same as that in sltm*
;;Each predicate in the skill will be extended to express all of its arguments in the given order.
;;This makes sure that a pair of a skill and its complete binding set decides a unique skill instance (task)
;;If a belief is changed by some of its arguments, then it is put in neg-effects and 
;;its new variation is put in pos-effects. Again, all the arguments of each effect will be extendedly shown.
(defstruct skill id head elements 
  pos-conditions neg-conditions tests 
  subskills pos-effects neg-effects)

(defparameter ccltm* nil)
(defparameter skills* nil)
(defparameter start-node* nil)
(defparameter pos-goals* nil)
(defparameter neg-goals* nil)
(defparameter open-queue* nil)
(defparameter current-node* nil)
(defparameter unfolded-goals* nil); will unfold the goals one level to their relations (if exist) to improve the goal heuristic
(defparameter goal-node* nil)
(defparameter hplan* nil)

;;A task is an instance of a skill determined by the skill and a full binding set.
(defstruct task head subtasks add-beliefs del-beliefs skill bindings)

(defun print-node (node &optional (title 'node))
  (when node
    (format t "~%~s:" title)
    (print-state (node-state node))
    (format t "~%HEURISTIC: ~s" (node-heuristic node))
    ;(print-task (first (node-htask node)))
    (print-htask (node-htask node))
    (format t "~%")
    (print-node (node-previous node) 'previous-node)))

(defun print-state (bstate &optional (title 'STATE))
  (format t "~%~s: " title)
  (princ (map 'list 'literal-head bstate)) 
  t)

(defun print-task (task)
  (when task
    (format t "~%TASK: ")
    (princ (task-head task))
    (print-state (task-add-beliefs task) 'add-beliefs)
    (print-state (task-del-beliefs task) 'del-beliefs)
    (values)))
    ;(format t "~%subtasks: ")
    ;(princ (task-subtasks task))))
  

(defun print-htasks (htasks)
  (when htasks (print-htask (first htasks))
             (print-htasks (rest htasks))))

(defun print-htask (htask)
  (when htask
    (print-task (first htask))
    (when (second htask)
      (format t "~%SUBTASKS: [")
      (print-htasks (second htask))
      (format t "]"))))
  
;;A literal is determined by an (fully substituted) instance of a concept head. 
;;So bindings is a complete binding set for the variables in the head only.
;;Note that there can be multiple binding sets (matching ways) for a concept to achieve a same belief (literal-head). 
;;Hence, we only store the partial binding set for the variables in the head of the concept.
;;The pos-dependencies is the set of concepts whose positive relations contain the concept.
;;An item in pos-dependencies is a (partially substituted) head of a concept whose relations contain the (head of) literal.
;;Note that the dependencies defined here differ from those defined in the cinstance structure.
;;The positivess/negativess is the set of (substituted using the partial binding set) positive/negative conditions of its cconcept. 
(defstruct literal head bindings concepts pos-dependencies pos-dependent-heads neg-dependencies neg-dependent-heads positivess negativess)

;;Htask is a hierarchical task. A htask is a list of two elements: the task and a list of htasks of its subtasks.

(defun reconstruct-attributes (attributes)
  "Get rid of 'is' from attributes"
  (loop for i from 0 to (- (/ (length attributes) 3) 1)
        collect (list (nth (* 3 i) attributes) (nth (+ (* 3 i) 2) attributes))))

(defun reconstruct (items)
  "Get rid of 'is'"
  (loop for i in items
        collect (list (car i) (third i))))

(defun refine-predicates (subskills)
  "Get rid of fieldnames '^...' from subskill-head"
  (loop for i in subskills
        collect (refine-predicate i)))

(defun reconstruct-elements (elements)
  "Get rid of 'is' and fieldnames '^...' from elements"
  (loop for i from 0 to (- (/ (length elements) 3) 1)
        collect (list (nth (* 3 i) elements) (refine-predicate (nth (+ (* 3 i) 2) elements)))))

(defun reconstruct-elements (elements)
  "Get rid of 'is' and fieldnames '^...' from elements"
  (loop for i in elements
        collect (list (car i) (refine-predicate (third i)))))

; Dongkyu's version with slightly more backward compatibility
; It now works with the old syntax in elements field of concepts (no 'is')
(defun reconstruct-elements (elements)
  "Get rid of 'is' and fieldnames '^...' from elements"
  (loop for i in elements
        collect (if (equal (second i) 'is)
		    (list (car i) (refine-predicate (third i)))
		  (list (second i) (refine-predicate i)))))

(defun add-elements (elements conditions)
  "Add predictes in :elements to conditions"
  (loop for i from (- (length elements) 1) downto 0
        do (setf conditions (cons (second (nth i elements)) conditions)))
  conditions)

(defun refine-predicate (predicate)
  "Eliminate field-names of attributes that start with '^'"
  (if (eq (second predicate) 'is) (setf predicate (third predicate)))
  (loop for i in predicate
        if (not (attributep i)) collect i))

;;In this version assumes that the ID/name of each object is inside the literal specifying it.
;;So the right side of each item in :elements is added in positives of the concept (or pos-conditions of skills)

(defun concept->cconcept (concept)
  "Convert concept to cconcept"
  (setf concept (make-cconcept :name (head-name (concept-head concept))
                            :attributes (reconstruct (concept-attributes concept))
                            :elements (reconstruct-elements (concept-elements concept))
                            :positives (concept-positives concept)
                            :negatives (concept-negatives concept)
                            :tests (concept-tests concept)
                            :arguments (head-values (concept-head concept)))
        (cconcept-positives concept) (add-elements (cconcept-elements concept) (cconcept-positives concept)))
  concept)

(defun get-positives (predicates)
  (loop for i in predicates
        if (not (eq (car i) 'not)) collect i))

(defun get-negatives (predicates)
  (loop for i in predicates
        if (eq (car i) 'not) collect (second i)))

(defun get-pos-effects (skill)
  (loop for i in (sclause-effects skill)
        if (not (eq (car i) 'not)) collect (refine-predicate i)))

(defun get-neg-effects (skill)
  "If some attributes of an object ?o changed then the literal indicating ?o before the action should disappear. So those literals are added to the negative effects by the second loop"
  (let* ((rs nil) (p nil) (elements (reconstruct-elements (sclause-elements skill))))
    (loop for i in (sclause-effects skill)
          if (eq (car i) 'not) 
          do (setf rs (cons (second i) rs)))
    (loop for i in (sclause-effects skill)
          if (eq (second i) 'is)
          do (setf p (assoc (car i) elements))
          (if p (setf rs (cons (second p) rs))))
    rs))

(defun sclause->skill (skill)
  "Convert sclause to skill"
 (setf skill (make-skill :id (sclause-id skill)
             :head (refine-predicate (sclause-head skill))
             :elements (reconstruct-elements (sclause-elements skill))
             :pos-conditions (refine-predicates (get-positives (sclause-conditions skill)))
             :neg-conditions (refine-predicates (get-negatives (sclause-conditions skill)))
             :tests (sclause-tests skill)
             :subskills (refine-predicates (sclause-subskills skill))
             :pos-effects (get-pos-effects skill)
             :neg-effects (get-neg-effects skill))
       (skill-pos-conditions skill) (add-elements (skill-elements skill) (skill-pos-conditions skill)))
 skill)

(defun initialize-search ()
  (clrhash literal-head-hash-set*)
  (clrhash lit-head->literal-hash*)
  (clrhash binding-hash-set*)
  (clrhash bindings-hash-set*)
  (clrhash taskid->task-hash*)  
  (clrhash state-hash*)
  (clrhash head-name->concepts-hash*)
  (setf ccltm* nil)

  (dolist (concept cltm*)
    (setf ccltm* (cons (concept->cconcept concept) ccltm*)))

  (dolist (concept ccltm*)
    (let* ((head-name (cconcept-name concept))
           (concepts (head-name->concepts head-name)))      
      (head-name->concepts-hash-add head-name (cons concept concepts))))

  (compute-all-concepts-dependencies)

 (dolist (skill sltm*)
    (setf skills* (cons (sclause->skill skill) skills*)))
  
  ;The input for unfold-goals is a set of literals, e.g., "((NOT (ONTABLE A ?TABLE)) (ON B A) (ON C B))"
 (let ((objectives (problem-objectives (first gstm*))))
   (setf unfolded-goals* (unfold-goals objectives)
	 pos-goals* (get-positives objectives)
	 neg-goals* (get-negatives objectives)))
 
; Dongkyu's change to make it work with PROBLEM structures 
;  (setf unfolded-goals* (unfold-goals gstm*)
;        pos-goals* (get-positives gstm*)
;        neg-goals* (get-negatives gstm*))

  (setf start-node* (make-node :state (get-initial-beliefs)))

  (compute-goal-heuristic start-node*)

 ;(sort-by-sxhash (node-state start-node*))
  (new-state-p (node-state start-node*))
  (if (goal-node-p start-node*) (setf goal-node* start-node*)
    (progn 
      (setf open-queue* (list start-node*) goal-node* nil)
      (format t "Expanding a node with heuristic value: "))))
       
(defun forward-search ()
  "Main search procedure for a plan."
  (initialize-search)  
  (loop until (or goal-node* (null open-queue*)) do
    (setf current-node* (first open-queue*) open-queue* (rest open-queue*))
    (format t "~d " (node-heuristic current-node*))
    (expand-current-node))
  (cond (goal-node* (setf hplan* (extract-plan goal-node* nil))
		    (format t "~%Found a plan!") t)
	(t (format t "~%No plan found!"))))


(defun extract-plan (node plan)
  (if (node-htask node)
      (extract-plan (node-previous node) (cons (node-htask node) plan))
    plan))

  
(defun expand-current-node ()
  "Expand the current (best open) node with all applicable tasks (matching skills)."
  (print-node current-node*)
  ;(read-char)
  (let ((match-tasks (match-all-possible-skills (node-state current-node*))))
    (dolist (task match-tasks)
      (generate-successor-node task)
      (if goal-node* (return)))))


(defun generate-successor-node (task)
  "Generate the sussessor node of the current-node given a task (matching-skill). This also instantiates the task into a htask."
  (let ((result (progress-a-task task (node-state current-node*))))
    (if result
	(let ((next-state (second result)))
	  (if (new-state-p next-state)
	      (let ((htask (first result))
		    ;;(new-node (make-node :state next-state :htask htask :previous current-node*)))
		    (new-node (make-node :state next-state :previous current-node*)))
		;;(print htask)
		(setf (node-htask new-node) htask)
		(compute-goal-heuristic new-node)
		;(print-node new-node)
		;(read-char)
		(if (goal-node-p new-node) (setf goal-node* new-node)
		  (setf open-queue* (insert-to-increasing-order-list new-node open-queue* :key #'node-heuristic)))))))))


(defun progress-a-task (task bstate)
  "Instantiate a task (skill instance) to return a htask and the next belief state given a belief state bstate"
  ;(format t "~%Level: ~s" level)
  (let* ((in-subtasks (task-subtasks task)) 
         (out-subtasks nil)
         (result (progress-subtasks in-subtasks out-subtasks bstate)))
    (unless (null result)
      (let* ((next-state (next-state task (second result)))
	     (htask (list task (first result))))
	(list htask next-state)))))
	

(defun progress-subtasks (in-subtasks out-subtasks bstate)
  (if (null in-subtasks) (list out-subtasks bstate)
    (let* ((result nil)
	   (subtasks (match-subtasks (first in-subtasks) bstate)))
      
      ;(format t "~%Level: ~s ~%State:" level)
      ;  (print-state bstate)   


      (loop for task in subtasks do
        
        ;(format t "~%level: ~s ~%subtask:" level)
        ;(print-task task)        

	(setf result (progress-a-task task bstate))

        ;(format t "~%~s" "result: ")
        ;(print result)
        ;(read-char)

	(if result
	    (setf result (progress-subtasks (rest in-subtasks) (append out-subtasks (list (first result))) (second result))))
	until result)
      result)))


(defun insert-to-increasing-order-list (item plist &key (key nil))
  "Insert an item to a list such that the keys of the elements are in an increasing order"
  (if (null plist) (cons item plist)
    (let ((less t))
      (if key
	  (if (> (funcall key item) (funcall key (first plist))) (setf less nil))
	(if (> item (first plist)) (setf less nil)))
      (if less (cons item plist)
	(cons (first plist) (insert-to-increasing-order-list item (rest plist) :key key))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; MATCHING, UNIFICATION, AND INSTANTIATION OF SKILLS AND CONCEPTS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun match-all-possible-skills (bstate)
  "Get tasks of all posible matching skill instances whose conditions are satisifed in the belief state bstate"
  (let ((match-tasks nil))
    ;(dolist (skill sltm*)
    (dolist (skill skills*)
      (setf match-tasks (append match-tasks (match-a-skill-to-tasks skill bstate nil))))
    match-tasks))

(defun match-a-skill-to-tasks (skill bstate bindings)
  "Match a skill to applicable tasks given a partial binding set (bindings)"
  (let* ((tasks nil)
	 ;(conditions (split-positive-negative-literals (sclause-conditions skill)))
	 ;(pos-conditions (first conditions))
	 ;(neg-conditions (second conditions))
	 (pos-conditions (skill-pos-conditions skill))
	 (neg-conditions (skill-neg-conditions skill))
         (tests (skill-tests skill))
         ;(ttt (if (and neg-conditions bindings) (break)))
	 (bindingss (match-predicates-beliefs pos-conditions bstate (list bindings) :neg-conditions neg-conditions :tests tests)))
    ;(print bindingss)
    (dolist (bindings bindingss)
      (let* ((taskid (list (skill-id skill) bindings))
	    (task (taskid->task taskid)))
	(unless task
	  (setf task (build-task skill bindings))
	  (taskid->task-hash-add taskid task))
	(setf tasks (cons task tasks))))
    tasks))
      
(defun build-task (skill bindings)
  "Build the task from a pair of a skill and a complete binding-set bindings"
  (let* ((task-head (binding-subst-eval (skill-head skill) bindings))
	 (task (make-task :head task-head :skill skill :bindings bindings)) 
	 (del-beliefs nil) (add-beliefs nil))
    (dolist (effect (skill-neg-effects skill))
     	  (setf effect (instantiate-predicate effect bindings)
		del-beliefs (cons effect del-beliefs)))
    (dolist (effect (skill-pos-effects skill))
	  (setf effect (instantiate-predicate effect bindings)
	        add-beliefs (cons effect add-beliefs)))
    (setf (task-del-beliefs task) del-beliefs
	  (task-add-beliefs task) add-beliefs)
    
    (dolist (subskill (skill-subskills skill))
      (setf subskill (binding-subst-eval subskill bindings)
	    (task-subtasks task) (append (task-subtasks task) (list (match-skills-with-head subskill)))))
    task))

(defun match-skills-with-head (skill-head-instance)
  "Get all pairs of skills and their partial binding sets given a skill-head-instance"
  (let ((matches nil) (a-match nil))
   (dolist (skill skills*)
     (setf a-match (get-bindings skill-head-instance (skill-head skill)))
     (if (first a-match)
	 (setf (first a-match) skill
	       matches (cons a-match matches))))
   matches))


(defun split-positive-negative-literals (literals)
  (let ((positive nil) (negative nil))
    (dolist (lit literals)
      (if (negative-p lit) (setf negative (cons (second lit) negative))
	(setf positive (cons lit positive))))
    (list positive negative)))


(defun match-predicates-beliefs (predicates bstate bindingss &key neg-conditions tests lit-head existence-check-only)
  "Get only bindings that satisy the negative conditions and tests. Then sort and add them to the binding set (hash-set)"
  (let* ((new-bindingss nil))
    (dolist (predicate predicates)
      (dolist (bindings bindingss)
	(setf new-bindingss (append new-bindingss (match-predicate-beliefs predicate bstate bindings))))
      (setf bindingss new-bindingss new-bindingss nil))
    (unless (null tests)
      (dolist (bindings bindingss)
        (if (physical-tested (binding-subst tests bindings))
            (setf new-bindingss (cons bindings new-bindingss))))
      (setf bindingss new-bindingss new-bindingss nil))
    
    (unless (null neg-conditions)
      (dolist (bindings bindingss)
        (if (neg-conditions-satisfied neg-conditions bindings bstate)
         (setf new-bindingss (cons bindings new-bindingss))))
      (setf bindingss new-bindingss))

    (if lit-head;;check if the belief lit-head is valid in the bstate with its conditions and tests
        (dolist (bindings bindingss)
          (let* ((concepts (head-name->concepts (first lit-head)))
                 (new-belief (build-literal-head (first concepts) bindings)))
            (if (eq new-belief lit-head) (return t)))) 
      (if existence-check-only
          (if (null neg-conditions) bindingss
            (dolist (bindings bindingss)
              (if (neg-conditions-satisfied neg-conditions bindings bstate) (return t))))
        (progn
          (if (null neg-conditions) (setf new-bindingss bindingss)
            (dolist (bindings bindingss)
              (if (neg-conditions-satisfied neg-conditions bindings bstate) 
                  (setf new-bindingss (cons bindings  new-bindingss)))))
          (loop for bindings in new-bindingss do
                (setf bindings (bindings-set-insert bindings))
                collect bindings))))))
   
    
(defun match-predicate-beliefs (predicate bstate bindings)
  "Match a predicate in a belief state (bstate) given a binding list and return a set of binding lists."
  (let* ((bindingss nil) (new-bindings nil) (literal nil) 
	 (new-predicate (binding-subst predicate bindings)))
    (dolist (literal bstate)
      (setf new-bindings (match-predicate-literal new-predicate (literal-head literal) bindings))
      (if new-bindings 
	  (if (second new-bindings) (setf bindingss (cons (second new-bindings) bindingss))
	    (progn
	      (setf bindingss (list bindings))
	      (return bindingss)))))
    bindingss))
   

(defun match-subpredicate-literal (predicate literal bindings)
 "Match a predicate with a literal given a partial binding set. Assume that all the object arguments must present in the defined order. Numeric attributes can be omitted but any present attributes must be in the given order." 
  (cond ((null predicate)  (list t bindings))
	((variable-p (first predicate))
	 (if (or (null (member (first literal) bindings :key #'rest)) (numberp (first literal))) ;;No two variables match to the same object constant in a literal
	     (let ((binding (binding-set-insert (cons (first predicate) (first literal)))))
	       (match-predicate-literal (rest predicate) (rest literal) (cons binding bindings)))))
	((eq (first predicate) (first literal))
	 (match-predicate-literal (rest predicate) (rest literal) bindings))
        ((fieldname-p (first predicate))
         (match-predicate-literal (rest predicate) (rest (member (first predicate) literal))  bindings))))

(defun match-predicate-literal (predicate literal bindings)
  "All arguments shown with no field-name"
  (cond ((or (null predicate) (null literal)) (if (eq  predicate literal) (list t bindings)))
	((variable-p (first predicate))
         (let ((binding (car (member (car predicate) bindings :key #'car))))
           (if (null binding)  
	 ;(if (null (member (first literal) bindings :key #'rest)) ;;No two variables match to the same constant in a literal
               (let ((binding (binding-set-insert (cons (first predicate) (first literal)))))
                 (match-predicate-literal (rest predicate) (rest literal) (cons binding bindings)))
             (if (eql (rest binding) (car literal))
                 (match-predicate-literal (rest predicate) (rest literal) bindings)))))
        ((eq (first predicate) (first literal))
	 (match-predicate-literal (rest predicate) (rest literal) bindings))))

(defun match-subtasks (skill-bindings-pairs bstate)
  (let ((subtasks nil))
    (dolist (pair skill-bindings-pairs)
      (setf subtasks (append subtasks (match-a-skill-to-tasks (first pair) bstate (second pair)))))
    subtasks))

(defun get-bindingss (pinstance predicates)
  "Get the set of binding sets each matches a predicate with the instance pinstance"
  (let* ((bindingss nil) (a-match nil) (bindings nil))
    (dolist (predicate predicates)
      (setf a-match (get-bindings pinstance predicate))
      (if a-match 
	  (setf bindings (bindings-set-insert (second a-match))
		bindingss (cons bindings bindingss))))
    bindingss))

(defun get-bindings (pinstance predicate)
  "Return the pair of t and the bindings that match predicate to pinstance if pinstance is an instance of predicate. Otherwise return nil"
  (if (eq (first pinstance) (first predicate))
      (let ((bindings nil))
	(get-binding-variables (rest pinstance) (rest predicate) bindings))))

(defun get-binding-variables (values variables bindings)
  (if (null values) (if (null variables) (list t bindings))
    (if variables
	(if (or (variable-p (first values)) (equal (first values) (first variables)))
	    (get-binding-variables (rest values) (rest variables) bindings)
	  (let* ((binding (binding-set-insert (cons (first variables) (first values))))
		 (bindings (cons binding bindings)))
	    (get-binding-variables (rest values) (rest variables) bindings))))))

(defun literal-head-from-cinstance (l-cinstance)
  "Get the literal header in the form (lit-name arg-value*) from a literal l-cinstance in the cinstance structure"
  (let* ((l-head (cinstance-head l-cinstance))
	(lname (head-name l-head))
	(arguments (head-values l-head))
	(bindings (head-bindings l-head)))
    (cons lname (binding-subst arguments bindings))))

(defun get-literal-head0 (concept bindings)
  "Get the literal header in the form (lit-name arg-value*) of a concept given a binding set."
  (let* ((c-head (concept-head concept))
	 (lname (head-name c-head))
	 (arguments (head-values c-head))
	 (lit-head (cons lname (binding-subst arguments bindings))))
    (literal-head-set-insert lit-head)))

(defun get-predicate (cconcept)
  (cons (cconcept-name cconcept) (cconcept-argument cconcept)))

(defun get-literal-head (cconcept bindings)
  "Get the literal header in the form (lit-name arg-values) of a concept given a binding set."
  (let* ((lname (cconcept-name cconcept))
	 (arguments (cconcept-arguments cconcept))
	 (lit-head (cons lname (binding-subst arguments bindings))))
    (literal-head-set-insert lit-head)))

(defun build-literal-head (cconcept bindings)
  "This is similar to the get-literal-head except it also computes the attributes in the head as the bindings may not contain those for them."
  (let ((attributes (binding-subst (cconcept-attributes cconcept) bindings)))
    (dolist (attribute attributes)
      (setf attribute (cons (first attribute) (evaluate (second attribute)))
            ;attr (print attribute)
            bindings (cons attribute bindings)))
    (get-literal-head cconcept bindings)))

(defun list-variable-replace (plist bindings)
  (if plist
      (let ((e (first plist)))
	(if (variable-p e)
	    (let ((v (binding-lookup e bindings)))
	      (if v (setf e v))))
	(cons e  (list-variable-replace (rest plist) bindings)))))

(defun binding-subst (plist bindings)
  (cond ((null plist) nil)
	((listp plist) (cons (binding-subst (first plist) bindings) (binding-subst (rest plist) bindings)))
	((variable-p plist) 
	 (let ((r (binding-lookup plist bindings)))
	   (if (null r) plist r)))
	(t plist)))

(defun binding-subst-eval (predicate bindings)
    (mapcar #'evaluate (binding-subst predicate bindings)))

(defun predicates-subst (predicates bindings)
  (let ((subst-predicates (binding-subst predicates bindings)))
    (loop for predicate in subst-predicates do
      (setf predicate (literal-head-set-insert predicate))
      collect predicate)))
    
	
(defun build-literal (concepts bindings)
  "Build a literal and save it to the hash table given a concept and a binding set only for variables in the head."
  (let* ((lit-head (get-literal-head (first concepts) bindings))
	 (new-lit (make-literal :head lit-head :bindings bindings :concepts concepts))
	 (positivess nil)
	 (negativess nil))
    (dolist (concept concepts)
      (setf positivess (cons (predicates-subst (cconcept-positives concept) bindings) positivess)
	    negativess (cons (predicates-subst (cconcept-negatives concept) bindings) negativess)))
    (setf (literal-positivess new-lit) positivess
	  (literal-negativess new-lit) negativess)
    (build-lit-pos-dependencies new-lit)
    (build-lit-neg-dependencies new-lit)
    (lit-head->literal-hash-add lit-head new-lit)
    new-lit))

(defun instantiate-predicate (predicate bindings)
  "Get or build (if not exists) a literal given a predicate (head name and variables) and a complete binding set"
  (let* ((lit-head (literal-head-set-insert (binding-subst-eval predicate bindings)))
	 (literal (lit-head->literal lit-head)))
    (if literal literal
      (let* ((concepts (head-name->concepts (first predicate)))	     
	     (head-bindings (second (get-binding-variables (rest lit-head) (cconcept-arguments (first concepts)) nil))))
	(build-literal concepts head-bindings)))))
    

(defun build-lit-pos-dependencies (literal)
  (let* ((head (literal-head literal))
	(dependent-head nil)
	(concept (first (literal-concepts literal)))
	(dependent-concepts (cconcept-pos-dependencies concept))
	(pos-dependencies nil)
	(pos-dependency nil)
	(pos-dependent-heads nil)
	(bindingss nil))
    (dolist (dependent-concept dependent-concepts)
      (setf bindingss (get-bindingss head (cconcept-positives dependent-concept)))
      (when bindingss
	(setf pos-dependency (list dependent-concept bindingss)
	      pos-dependencies (cons  pos-dependency pos-dependencies))      
	(dolist (bindings bindingss)
	  (setf dependent-head (get-literal-head dependent-concept bindings))
	  (setf pos-dependent-heads (adjoin dependent-head pos-dependent-heads :test 'eq)))))
    (setf (literal-pos-dependencies literal) pos-dependencies
	  (literal-pos-dependent-heads literal) pos-dependent-heads)))


(defun build-lit-neg-dependencies (literal)
  (let* ((head (literal-head literal))
	(dependent-head nil)
	(concept (first (literal-concepts literal)))
	(dependent-concepts (cconcept-neg-dependencies concept))
	(neg-dependencies nil)
	(neg-dependency nil)
	(neg-dependent-heads nil)
	(bindingss nil)
	(head-bindingss nil))
    (dolist (dependent-concept dependent-concepts)
      (setf bindingss (get-bindingss head (cconcept-negatives dependent-concept)))
      (when bindingss
	(setf head-bindingss nil)
	(dolist (bindings bindingss)	  
	  (setf dependent-head (get-literal-head dependent-concept bindings)
		bindings (second (get-binding-variables (rest dependent-head) (cconcept-arguments dependent-concept) nil))
		bindings (bindings-set-insert bindings)
		head-bindingss (adjoin bindings head-bindingss :test 'eq)
		neg-dependent-heads (adjoin dependent-head neg-dependent-heads :test 'eq)))
	(setf neg-dependency (list dependent-concept head-bindingss)
	      neg-dependencies (cons neg-dependency neg-dependencies))))
    (setf (literal-neg-dependencies literal) neg-dependencies
	  (literal-neg-dependent-heads literal) neg-dependent-heads)))


(defun compute-all-concepts-dependencies ()
  "Get the positive and negative dependencies for all concepts. A dependency of a concept is another concept whose relations contain the concept."
  (dolist (c ccltm*)
    (setf (cconcept-pos-dependencies c) (get-pos-dependencies c)
          (cconcept-neg-dependencies c) (get-neg-dependencies c))))

(defun element-of (lit-head concept)
  "Check whether the given concept has an element with head 'lid-head'. This does not count the element defines itself"
  (unless (and (= (length (cconcept-elements concept)) 1) (eq (cconcept-name concept) (car (second (car (cconcept-elements concept))))))
    (loop for e in (cconcept-elements concept)
          if (eq (car (second e)) lit-head) return t))) 

(defun get-pos-dependencies (concept)
  "Get the sets of concepts whose positives contain a literal with the given name."
  (loop for c in ccltm*
        if (and (not (eq c concept)) (or (assoc (cconcept-name concept) (cconcept-positives c)) (element-of (cconcept-name concept) c)))
        collect c))

(defun get-neg-dependencies (concept)
  "Get the sets of concepts whose negatives contain a literal with the given name."
  (loop for c in ccltm*
        if (and (not (eq c concept)) (assoc (cconcept-name concept) (cconcept-negatives c)))
        collect c))


;;When adding a belief to a belief state, the belief's pos-dependencies, 
;;the literals that have the added belief in its positive relations, may become new beliefs in the new belief state. 
;;Similarly, removing a belief may create new beliefs due to the belief's neg-dependencies. 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun add-dependent-beliefs (added-removed-belief bstate &key removed)
  "Compute the beliefs whose positive/negative relations contain a recently added/removed literal to/from the belief state and their relations are satisfied in the belief state. The removed argument indicates the belief was removed from bstate."
  (let* ((new-beliefs nil) 
	 (new-bstate bstate) 
	 (dependencies (literal-pos-dependencies added-removed-belief)))
    (if removed (setf dependencies (literal-neg-dependencies added-removed-belief)))
    (dolist (dependency dependencies)
      (let* ((concept (first dependency)) 
	     (bindingss (second dependency)))
	(setf new-beliefs (append new-beliefs (match-a-concept-to-literals concept new-bstate bindingss))
	      new-bstate (append bstate new-beliefs))))
	
    (list new-bstate new-beliefs)))

;;Removing a belief from a belief state may invalidate other beliefs whose positive relations contains the removed belief.
;;Similarly, adding a belief to a belief state may invalidate beliefs whose negative relations contains the added belief.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun remove-dependent-beliefs (added-removed-belief bstate &key removed)
  "Return the set of beliefs in bstate such that the added/removed literal is an instance of a concept of their negative/positive relations."
  (let* ((removed-beliefs nil) 
	 (dependent-heads (literal-neg-dependent-heads added-removed-belief)))
    (if removed (setf dependent-heads (literal-pos-dependent-heads added-removed-belief)))
    (dolist (dependent-head dependent-heads)
      (dolist (belief bstate)
	(if (instance-of-p (literal-head belief) dependent-head)
	    (let* ((concepts (literal-concepts belief))   
                   (positivess (literal-positivess belief))
		   (negativess (literal-negativess belief))
		   (head-bindingss (list (literal-bindings belief)))
		   (matched nil))
	      (loop for concept in concepts for positives in positivess for negatives in negativess do		
		(setf matched (match-predicates-beliefs positives bstate head-bindingss :neg-conditions negatives :tests (cconcept-tests concept) :lit-head (literal-head belief) :existence-check-only t))
		until matched)
	      (unless matched
		(setf removed-beliefs (cons belief removed-beliefs)
		      bstate (remove belief bstate)))))))
    (list bstate removed-beliefs)))


(defun match-a-concept-to-literals (concept bstate bindingss)
  "Match a concept to new beliefs by the relations/conditions given a set of partial binding sets (bindingss)"
  (let* ((new-beliefs nil) (new-lit nil) (lit-head nil) (head-bindings nil)
	 (positives (cconcept-positives concept))
	 (negatives (cconcept-negatives concept))
         (tests (cconcept-tests concept))
	 (concepts (head-name->concepts (cconcept-name concept)))
	 (new-bindingss (match-predicates-beliefs positives bstate bindingss :neg-conditions negatives :tests tests)))
    (dolist (bindings new-bindingss)
      (setf lit-head (build-literal-head concept bindings) 
	    new-lit (lit-head->literal lit-head))
      (if new-lit 
	  (unless (or (member new-lit bstate :test 'eq) (member new-lit new-beliefs :test 'eq));;avoid getting duplicate literals by multiple matching ways. 
	    (setf new-beliefs (cons new-lit new-beliefs)))	

	(setf head-bindings (second (get-binding-variables (rest lit-head) (cconcept-arguments concept) nil))
	      new-lit (build-literal concepts head-bindings)
	      new-beliefs (cons new-lit new-beliefs))))
    new-beliefs))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;; HASHING, SET  UTILITIES 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun concat-syms (&rest syms)
  "Concatenate a sequence of symbols to a symbol, e.g., 'A 'B '1 -> 'AB1"
  (intern (apply #'concatenate 'string (mapcar #'write-to-string syms))))

(defun create-symbol-id (sym id)
   (intern (concatenate 'string (string-upcase (symbol-name sym)) (write-to-string id))))

(defun sort-by-sxhash (plist)
   (sort plist '< :key #'sxhash))

(defmacro bidirectional-hash (keyname test-function)
  `(progn (defparameter ,(concat-syms keyname '->id-hash*) (make-hash-table :test ,test-function)) 
	  (defparameter ,(concat-syms 'id-> keyname '-hash*) (make-hash-table :test 'equal))  
	  (defun  ,(concat-syms keyname '->id-hash-add) (,keyname) 
	    (let ((id (,(concat-syms keyname '->id) ,keyname)))
	      (unless id    
		(setf id (hash-table-count ,(concat-syms keyname '->id-hash*))
		      (gethash ,keyname ,(concat-syms keyname '->id-hash*)) id
		      (gethash id ,(concat-syms 'id-> keyname '-hash*)) ,keyname))
	      id))
	  (defun  ,(concat-syms keyname '-hash-add) (,keyname) 
	    (let ((id (,(concat-syms keyname '->id) ,keyname)))
	      (if id (gethash id ,(concat-syms 'id-> keyname '-hash*))
		(setf id (hash-table-count ,(concat-syms keyname '->id-hash*))
		      (gethash ,keyname ,(concat-syms keyname '->id-hash*)) id
		      (gethash id ,(concat-syms 'id-> keyname '-hash*)) ,keyname))))
	  (defun  ,(concat-syms 'id-> keyname) (id)
	    (gethash id ,(concat-syms 'id-> keyname '-hash*)))
	  (defun  ,(concat-syms keyname '->id) (,keyname)
	    (gethash ,keyname ,(concat-syms keyname '->id-hash*)))))

(defmacro hash-set (keyname test-function)
  `(progn (defparameter ,(concat-syms keyname '-hash-set*) (make-hash-table :test ,test-function)) 
	  (defun  ,(concat-syms keyname '-set-insert) (,keyname &optional (check-existence t))
	    (if check-existence 
		(let ((member (gethash ,keyname ,(concat-syms keyname '-hash-set*))))
		  (if member member 
		    (setf (gethash ,keyname ,(concat-syms keyname '-hash-set*)) ,keyname)))))
	  (defun ,(concat-syms keyname '-set-find) (,keyname)
	    (gethash ,keyname ,(concat-syms keyname '-hash-set*)))))

(defmacro hash-to-data (key data test-function)
  `(progn (defparameter ,(concat-syms key '->  data '-hash*) (make-hash-table :test ,test-function)) 
	  (defun  ,(concat-syms key '-> data '-hash-add) (,key ,data) 
	    (setf (gethash ,key ,(concat-syms key '-> data '-hash*)) ,data))
	  (defun  ,(concat-syms key '-> data) (,key) 
	    (gethash ,key ,(concat-syms key '-> data '-hash*)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;REPRESENTATION: BELIEFS, BINDINGS, TASKS (with closed-world-assumption)
;;We use HASH-TABLE and HASH-SET utilities to keep each binding, binding-set, literal, or task at only ONE PLACE in memory.
;;This way we reduce both memory consumption and computation time in general. For example, given a skill and its complete 
;;binding-set, we hash the pair to lookup for its task. If the task already created (exists in the hash-table) we then do not need
;;to create the task again but use the existing one indtead. 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;Create the set for storing (later) generated literals that must be distinct
;;A lit-head is the substitution of the concept head  with a binding set
(hash-to-data lit-head literal 'equalp)

;;Create the set for storing incomplete substitutions of literal heads
(hash-set literal-head 'equalp)

;;Create the set for generated bindings of the form (?variable value)
(hash-set binding 'equalp)

;;Create the set for generated binding-sets (sorted lists)
(hash-set bindings 'equal)

;;Create the hash-table for tasks. A taskid is the list of the skill id and a binding set.
(hash-to-data taskid task 'equal)

;;Create the hash-table for hashing a concept given its head-name.
(hash-to-data head-name concepts 'eq)

;;Create a hash-table that maps (the state of) a search-node to true (t) if it does not exist.
;;A belief state is a list of non-negative integers in increasing order.
(defparameter state-hash* (make-hash-table :test 'equal))

(defun new-state-p (bstate)
  "Check whether the state already exists (in the hash table). If not then add it to the hash-table."  
  (let* ((new-bstate (copy-list bstate))  
	 ;(sort-by-sxhash new-bstate)
	 (new-bstate (sort new-bstate '< :key #'(lambda (lit) (sxhash (literal-head lit)))))
	 (existing (gethash new-bstate state-hash*)))
    (if (not existing) (setf (gethash new-bstate state-hash*) t))
    (not existing)))

(defun negative-p (literal)
  ;;Check whether a literal is negative (a negation of a proposition)
  (eq 'not (first literal)))

(defun get-initial-beliefs ()
  "Get the set of literals in the initial belief state"
  (let* ((init-bstate nil) (new-lit nil))
    (dolist (cinst cstm*)
      (let* ((head-name (head-name (cinstance-head  cinst)))
	     (bindings (head-bindings (cinstance-head  cinst)))
	     (concepts (head-name->concepts head-name)))	
	(setf new-lit (build-literal concepts bindings)
	      init-bstate (cons new-lit init-bstate))))	    
    init-bstate))
		  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; SATISFACTION CHECKING, BELIEF UPDATE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(defun variable-p (x) (string= (symbol-name x)  "?" :end1 1))

(defun variable-p (x)
  "Is x a variable (a symbol beginning with `?')?"
  (and (symbolp x) (equal (elt (symbol-name x) 0) #\?)))

(defun fieldname-p (x)
  "Is x a fieldname (a symbol beginning with `^')?"
  (and (symbolp x) (equal (elt (symbol-name x) 0) #\^)))

(defun get-component (component-name plist)
  "Get the value of a component from a list plist given its name component-name"
  (second (member component-name plist)))

(defun binding-lookup (x bindings)
  "Get the bound value of a variable given a binding set, e.g., (binding-lookup 'y '((x . a) (y . b) (z . c))) returns b"
  (rest (assoc x bindings)))

(defun copy-component (component-name plist)
  (copy-list (get-component component-name plist)))

(defun predicate-equal (p1 p2)
  (if (negative-p p1) (if (negative-p p2) (predicate-equal (second p1) (second p2)))
    (and (instance-of-p p1 p2) (instance-of-p p2 p1))))

(defun predicate-subsumed-p (l li)
  "Edxtending for negative predicate: (not p) is an instance of (not p1) iff p1 is an instance of p."
  (if (negative-p li) (if (negative-p l) (instance-of-p (second l) (second li)))
    (instance-of-p li l)))

(defun instance-of-p (li l)
  "Check whether a positive literal li is an instance of (or equal to) a literal l"
  (cond ((null li) (null l))
	((or (variable-p (first l)) (eq (first li) (first l))) (instance-of-p (rest li) (rest l)))))

(defun instance-among-p (li ls)
  (if ls
      (if (instance-of-p li (first ls)) t (instance-among-p li (rest ls))))) 

(defun literal-satisfied (literal beliefs)
  "Check whether a literal is satisfied in a belief state represented by the set of their heads. Also consider literals with variables"
  (if (negative-p literal)
      (not (literal-satisfied (second literal) beliefs))
    (let ((satisfied nil))
      (loop for belief in beliefs do
	  (setf satisfied (instance-of-p (literal-head belief) literal))
	until satisfied)
     satisfied)))
    

(defun literals-satisfied (literals beliefs)
  "Check whether a set of literals is satisfied in a belief state. Also considering literals with variables in the set"
  (let ((satisfied t))
    (loop for literal in literals do
      (setf satisfied (literal-satisfied literal beliefs))
       until (not satisfied))
    satisfied))

;;A formula is define as follow: 
; 0- nil: its value is true (we denote this for the case there is no condition then the condition is always satisfied)
; 1- a predicate: its value its true iff there exists a belief which is an instance of  its instance with the given binding set
; 2- a (conjunctive) list of formulae: it is true iff all the formulae in the list are true.    
; 3- a negation of a formula of the form (not F): (not F) is true iff F is nil
; 4- We do not use disjunction in the formula. But a disjunction can be converted to an equivalent formula, 
; e.g., (or f1 f2) is equivalent to (not ((not f1) (not f2)))  

(defun formula-satisfied (formula bindings beliefs)
  "Check whether a general formula, given a binding set, is satisfied in a belief state."
  (print 'EVALUATE)
  (print formula)
  (cond ((null formula) t) 
	((eq (first formula) 'not) (not (formula-satisfied (second formula) bindings beliefs)))
	((listp (first formula))  (if (formula-satisfied (first formula) bindings beliefs)
				      (formula-satisfied (rest formula) bindings beliefs)))
	(t (literal-satisfied (binding-subst formula bindings) beliefs))))


(defun neg-conditions-satisfied0 (predicates bindings beliefs)
  "Check whether a set of negative literals given by their predicates and bindings is satisfied in a belief state."
  (let ((satisfied nil))
    (loop for predicate in predicates do
      (setf satisfied (literal-satisfied (binding-subst predicate bindings) beliefs))
       until satisfied)
    (not satisfied)))

(defun neg-conditions-satisfied1 (conditions bindings bstate)
  "Check whether a set of negative conditions, where each condition can be either a single predicate or a list of predicates, is satisfied in a belief state with a given binding set."
  (let ((satisfied nil))
    (loop for predicate in conditions do
      (if (listp (first predicate)) 
	  (setf satisfied (match-predicates-beliefs predicate bstate (list bindings)))
	(setf satisfied (literal-satisfied (binding-subst predicate bindings) bstate)))
      until satisfied)
    (not satisfied)))

(defun neg-conditions-satisfied (conditions bindings bstate)
  "Check whether any of negative conditions is satisfied in a belief state with a given binding set."
  (if (null conditions) t
    (if (match-predicate-beliefs (first conditions) bstate bindings) nil
	(neg-conditions-satisfied (rest conditions) bindings bstate))))

(defun instance-count (predicate beliefs)
  "Count the number of instances of predicate in beliefs"
  (let ((count 0))
     (dolist (belief beliefs)
       (if (instance-of-p (literal-head belief) predicate) (setf count (1+ count))))
    count))


(defun number-satisfied (literals beliefs)
  "Return the number of literals in a set of literals that are satisfied in a belief state"
   (let ((count 0))
    (dolist (literal literals)
      (if (literal-satisfied literal beliefs) (setf count (1+ count))))
    count))


(defun next-state (task bstate)
  "Return the successor-state of the execution of a skill instance in a state"
  ;(print 'computing-next-state-of)
  ;(print-state bstate) 
  ;(print-task task)
 
  (let* ((add-set (task-add-beliefs task)) 
	 (del-set (task-del-beliefs task))
	 (result nil)
	 (bstate1 nil)
	 (new-bstate (union (set-difference bstate del-set :test #'eq) add-set :test #'eq)))
    
    (loop do ;;compute deductive closure
      (setf bstate1 new-bstate)
      (dolist (added-belief add-set)
	(setf result (remove-dependent-beliefs added-belief new-bstate))
	(when (second result)
	  (setf new-bstate (first result)
		del-set (append del-set (second result))))
	(setf result (add-dependent-beliefs added-belief new-bstate))
	(when (second result)
	  (setf new-bstate (first result)
		add-set (append add-set (second result)))))
      (dolist (removed-belief del-set)
	(setf result (remove-dependent-beliefs removed-belief new-bstate :removed t))
	(when (second result)
	  (setf new-bstate (first result)
		del-set (append del-set (second result))))
	(if (intersection add-set del-set) (break "Adding and removing same belief"))
	(setf result (add-dependent-beliefs removed-belief new-bstate :removed t))
	(when (second result)
	  (setf new-bstate (first result)
		add-set (append (second result) add-set))))
      until (eq new-bstate bstate1))     
    new-bstate))


(defun goal-node-p (node)
  "Check whether a node is a goal node, i.e., there is no goal unsatisfied in the state of the node"
 ;(zerop (node-heuristic node)))
  (let* (;(positives (problem-pos-objectives (first gstm*)))
	 ;(negatives (map 'list #'second (problem-neg-objectives (first gstm*))))
	 (bstate (node-state node)))	 
    (match-predicates-beliefs pos-goals* bstate (list nil) :neg-conditions neg-goals* :existence-check-only t)))

  
(defun compute-goal-heuristic0 (node)
  "Compute the number of goals unsatisfied in the belief state of the node" 
  (let* ((bstate (node-state node))
	 (goals (problem-objectives (first gstm*)))
	 (count 0))
    (dolist (goal goals)
      (if (negative-p goal)
	  (setf count (+ count (instance-count (second goal) bstate)))
	  (if (not (literal-satisfied goal bstate)) (setf count (1+ count)))))
    (setf (node-heuristic node) count)))

(defun compute-goal-heuristic1 (node)
  "Compute the number of goals unsatisfied in the belief state of the node" 
  (let* ((bstate (node-state node))
	 (count 0))
    (dolist (goal unfolded-goals*)
      (if (negative-p goal)
	  (setf count (+ count (instance-count (second goal) bstate)))
	  (if (not (literal-satisfied goal bstate)) (setf count (1+ count)))))
    (setf (node-heuristic node) count)))

(defun compute-goal-heuristic (node)
  "Compute the number of goals unsatisfied in the belief state of the node" 
  (let* ((bstate (node-state node))
	 (count 0))
    (dolist (goal unfolded-goals*)
      (cond ((negative-p goal) (setf count (+ count (instance-count (second goal) bstate))))
	    ((not (listp (first goal))) (if (not (literal-satisfied goal bstate)) (setf count (1+ count))))
	    ((not (literal-satisfied (first goal) bstate))
	     (let* ((subcount 0) (relations (second goal)) (bindings (third goal)))
	       (dolist (predicate relations)
		 (if (negative-p predicate)
		     (setf subcount (+ subcount (length (match-predicate-beliefs (second predicate) bstate bindings))))
		   (if (not (literal-satisfied predicate bstate))
		       (setf subcount (1+ subcount)))))
	       (if (zerop subcount) (setf count (1+ count))
		 (setf count (+ count subcount)))))))
    (setf (node-heuristic node) count)))

(defun unfold-goals (goals)
  "Unfold positive goals one level to improve the goal-heuristic."
  (let ((new-goals nil))
    (dolist (goal goals)
      (if (negative-p goal) (setf new-goals (cons goal new-goals))
	(let* ((concepts (head-name->concepts (first goal)))
	       (relations (cconcept-positives (first concepts))))
	  (if (or (rest concepts) (null relations)) (setf new-goals (cons goal new-goals))
	    (let* ((head-bindings (second (get-binding-variables (rest goal) (cconcept-arguments (first concepts)) nil)))
		  (r-goals (binding-subst relations head-bindings))
		  (goal (list goal r-goals head-bindings)))
	      (setf new-goals (cons goal new-goals)))))))
    new-goals))


(defun subsume-join (predicate plist)
  "Add a predicate to a list if it is not subsumed by any in the list, e.g. not add (on A ?X) if there is (on A B) and not add (not (on A B)) if there is (not (on A ?X)) in the list. On the other hand, if (on A B) is added then (on A ?X) should be removed from the list."
  (if (member predicate plist :test 'predicate-subsumed-p) plist
    (let ((result nil))
      (loop for pe in plist do
	(unless (predicate-subsumed-p pe predicate)
	  (setf result (cons pe result))))
      (cons predicate result))))
  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;MATCHING CONCEPTS, COMPUTE BELIEFS AND DEDUCTIVE CLOSURE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun binding (percept record)
  "Collect the (variable object) mapping pairs given a percept and a data record, assuming that the orders of the components in the percept and in the primitive data record are the same"
  (let ((binding nil) (pair nil))
    (loop until (equal percept nil) do
      (setf record (member (first percept) record))
      (when (equal record nil)
	(setf binding nil)
	(return))
      (setf pair (list (second percept) (second record)))
      (setf binding (append binding pair))
      (setf percept (rest (rest percept))))
    binding))


(defun match-concepts (concepts data beliefs)
   "Collect all the possible predicate instances given a list of concepts and the current state (symbolic and physical primitive)"
   ;;Assume that the set of beliefs is monotonically increasing during the computation, i.e., no belief is removed from the set of beliefs
   ;;The first round should collect all the instances of predicates with no relations then later rounds should consider only predicates with relations 
   (dolist (concept concepts)  (match-a-concept concept data beliefs))
   (let ((belief-count (length beliefs)) (old-count 0))
     (loop do
       (setf old-count belief-count)
       (dolist (concept concepts)  
	  (if (get-component ':relations concept)
	      (match-a-concept concept data beliefs)))
       (setf belief-count (length beliefs))
	until (equal belief-count old-count)))) 
       

(defun match-a-concept0 (concept data beliefs)
  "Collect all the possible predicate instances given a concept and the current state (symbolic and physical primitive)"
  (let ((percepts (get-component ':percepts concept))
	(bindings nil))
    (matching-a-concept concept data percepts bindings beliefs)))  
    
(defun predicate-existing-p (concept binding beliefs)
  (let ((predicate (get-instance (first concept) binding)) (id (literal->id predicate)))
    (not (or (null id) (null (member id beliefs))))))

(defun get-instance (obj-structure binding)
   (if obj-structure
      (let ((i (first obj-structure)) (r (rest obj-structure)))
	(if (listp i)
	    (append (list (get-instance i binding)) (get-instance r binding))
	  (progn
	    (let ((pair (assoc i binding)))
	      (if pair (setf i (rest pair))))
	    (append (list i) (get-instance r binding)))))))

(defun radical-copy-list (plist) 
  (let ((clist (copy-list plist)))
    (dolist (i clist)
      (if (listp i) (setf i (radical-copy-list i))))
    clist))

(defun matching-a-concept (concept data percepts bindings beliefs)
  "Elaborate the match-a-concept in a recursive manner"
  (if (not (predicate-existing-p concept bindings beliefs))
      (if (null percepts)	
	  (let ((predicate (get-instance (first concept) bindings))
		(relations (get-instance (get-component ':relations concept) bindings))
		(tests (get-instance (get-component ':tests concept) bindings)))
	    (when (and (literals-satisfied relations beliefs) (physical-tested tests))
		(push (literal->id-hash-add predicate) beliefs)))
	(let ((len (length data)))
	  (dotimes (i len)
	    (let ((record (nth i data)) (binding (binding (first percepts) record)))
	      (if binding 
		  (let ((bindings (append bindings binding)) 
			 (data (append (subseq data 0 i) (subseq data (1+ i) len))))
		    (matching-a-concept concept data (rest percepts) bindings beliefs)))))))))
  

(defun physical-tested (tests)
  (let ((result t) (test (first tests)))
    (when (not (null test))
      (setf result (evaluate test))
      (if result (setf result (physical-tested (rest tests)))))
    result))


(defun evaluate0 (lf)
  "Evaluate a formula given as a list, e.g., (+ 2 3 (* 4 5)) is evaluated as 25, or a symbol, e.g., 5 is evaluated as 5"
  (if (listp lf)
      (let ((param	     (loop for i in (rest lf)
	       collect (evaluate i))))
	(apply (first lf) param))
    lf))

(defun equalpp (a b) ;used to compare two literals containing numeric attributes
  (if (null a)
      (null b)
    (if (not (listp a))
        (or (equalp a b)
            (and (numberp a) (numberp b) (< (abs (- a b)) 0.00001)))
      (and (listp b)
           (equalpp (car a) (car b))
           (equalpp (cdr a) (cdr b))))))
    
(defun evaluate1 (lf)
  "Evaluate a formula given as a list, e.g., (+ 2 3 (* 4 5)) is evaluated as 25, or a symbol, e.g., 5 is evaluated as 5"
  (if (and (listp lf) lf)
      (if (eq (car lf) 'not) (not (evaluate (second lf)))
        (let* ((func (first lf)) (param nil) (all-numberp t))
          (loop for i in (rest lf) do
                (setf i (evaluate i))
                (if (numberp i) (setf param (cons i param))
                  (progn (setf all-numberp nil)
                    (return))))
          (if all-numberp (apply func (reverse param)) nil)))
    lf))


(defun evaluate (lf)
  "Evaluate a formula given as a list, e.g., (+ 2 3 (* 4 5)) is evaluated as 25, or a symbol, e.g., 5 is evaluated as 5"
  (if (and (listp lf) lf)
      (if (eq (car lf) 'not) (not (evaluate (second lf)))
	(if (eq (car lf) 'or) (or (evaluate (second lf)) (evaluate (rest (rest lf))))
		(let* ((func (first lf)) (param nil) (all-numberp t))
		  (loop for i in (rest lf) do
			(setf i (evaluate i))
			(if (numberp i) (setf param (cons i param))
			  (progn (setf all-numberp nil)
			    (return))))
		  (if all-numberp (apply func (reverse param)) nil))))
    lf))

