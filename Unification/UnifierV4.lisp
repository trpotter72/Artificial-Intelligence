;;*****************************************************************************
;;  Unifier V4
;;  Adapted and Implemented with Peter Norvig's
;;  Paradigms of Artificial Intelligence Programming
;;*****************************************************************************
;;
;;V4 adds the notion of clauses and uses them to build up a prolog style
;;logic interpreter
;;
;;


(defconstant fail nil "Indicates matching failure")

(defconstant no-bindings '((t.t)) "Indicates match with no bindings")

(defparameter *occurs-check* t "Check for infintely recursing structures?")

(defvar *db-predicates* nil
  "All list of all the predicates currently stored in the database")

(defun clear-db ()
  "Remove all clauses for all predicates from the data base"
  (mapc #'clear-predicate *db-predicates*))

(defun clear-predicate (predicate)
  "Remove the clause for a single predicate"
  (setf (get predicate 'clauses) nil))

(defmacro <- (&rest clause)
  "Add a clause to the data base."
  '(add-clause ',clause))

(defun clause-head (clause) (first clause))

(defun clause-body (clause) (rest clause))

(defun add-clause (clause)
  "Add a clause to the db, indexed w/ clause head"
  ;;The predicate must be a non-variable symbol
  (let ((pre (predicate (clause-head clause-head))))
    (assert (and (symbolp pred) (not (variable-p pred))))
    (pushnew pred *db-predicates*)
    (setf (get pred 'clauses)
          (nconc (get-clauses pred) (list clauses)))
    pred))

(defun variable-p (x)
  "Is a variable (symbol beggining with '?'"
  (and (symbolp x) (equal (char (symbol-name x) 0) #\?)))

(defun get-binding (var bindings)
  "Find a (var . val) pair in a bindings list"
  (assoc var bindings))

(defun binding-val (binding)
  "Return the val of the (var . val) pair"
  (cdr binding))

(defun lookup (var bindings)
  "Get the value of a variable from the list of bindings"
  (binding-val (get-binding var bindings)))

(defun extend-bindings (var val bindings)
  "Add a (var . val) pair to the bindings list"
  (cons (cons var val)
        (if (eq bindings no-bindings)
            nil
            bindings)))

(defun match-variable (var input bindings)
  "Does the var match? Uses or updates and returns binings"
  (let ((binding (get-binding var bindings)))
    (cond ((not binding)
           (extend-bindings var input bindings))
          ((equal input (binding-val binding)) bindings)
          (t fail))))


(defun occurs-check (var x bindings)
  "Check to see if a possible binding references itself within to recuse"
  (cond ((eq var x) t)
        ;if x is a variable simplify and check again
        ((and (variable-p x) (get-binding x bindings))
         (occurs-check var (lookup x bindings) bindings))
        ;if x is a list structure, check both the first element and the rest
        ((consp x)
         (or (occurs-check var (first x) bindings)
             (occurs-check var (rest x) bindings)))

        ;should all of these fail, var is not referenced within x
        (t nil)))


(defun unifier (x y)
  "Unifies two variable clauses(?) and outputs a clause in lowest terms"
  (subst-bindings (unify x y) x))

(defun unify (x y &optional (bindings no-bindings))
  "See if x and y match with the given bindings"
  (cond ((eq bindings fail) fail)
        ((eql x y) bindings)
        ((variable-p x) (unify-variable x y bindings))
        ((variable-p y) (unify-variable y x bindings))
        ((and (consp x) (consp y))
         (unify (rest x) (rest y)
              (unify (first x) (first y) bindings)))
        (t fail)))

(defun unify-variable (var x bindings)
  "Unify var with x, this uses and may update bindings"
  (cond ((get-binding var bindings)
         (unify (lookup var bindings) x bindings))
        ((and (variable-p x) (get-binding x bindings))
         (unify (lookup x bindings) var bindings))
        ;Trying to bind an infinite recursive structure
        ((and *occurs-check* (occurs-check var x bindings)) fail)
        (t (extend-bindings var x bindings))))

(defun subst-bindings (bindings x)
  "Recursively rebinds variables to the lowest possible binding"
  (cond ((eq bindings fail) fail)
        ((eq bindings no-bindings) x)
        ((and (variable-p x) (get-binding x bindings))
         (subst-bindings bindings (lookup x bindings)))
        ((atom x) x)
        (t (cons (subst-bindings bindings (first x))
                 (subst-bindings bindings (rest x))))))

(defun prove (goal bindings)
  "Return a list of possible solutions to a goal"
  (mapcan #'(lambda (clause)
              (let ((new-clause (rename-variables clause)))
                (prove-all (clause-body new-clause)
                           (unify goal (clause-head new-clause) bindings))))
          (get-clauses (predicate goal))))

(defun prove-all (goals bindings)
  "Return a list of solutions to the conjunction of goals"
  (cond ((eq bindings fail) fail)
        ((null goals) (list bindings))
        (t (mapcan #'(lambda (goal1-solution)
                       (prove-all (rest goals) goal1-solution))
                   (prove (first goals) bindings)))))


;;Bugs:
;;
;;  One can create an infinite recursive sub-structure using
;;
;;    (unify '?x '(a b c ?x))
;;
;;  This is beacuse the binding (?x . (a b c ?x)) is created to unify this
;;  type of structure, we would need a method to represent this infintely
;;  recursing structure (or a LOT of memory).
;;
;;Solutions:
;;
;;  Rather than develop an actual solution to the above problem, this type of
;;  input will be disallowed (if we need infinte structures, we can make them
;;  later) ARE YOU READY TO LOOK AT V3?!? It's about to get awesome
;;
