;;*****************************************************************************
;;  Unifier V2
;;  Adapted and Implemented with Peter Norvig's
;;  Paradigms of Artificial Intelligence Programming
;;*****************************************************************************
;;
;;Second version attempts to fix the infinite loop possible when a binding
;;references itself (directly or indirectly)
;;


(defconstant fail nil "Indicates matching failure")

(defconstant no-bindings '((t.t)) "Indicates match with no bindings")

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
        (t (extend-bindings var x bindings))))

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
