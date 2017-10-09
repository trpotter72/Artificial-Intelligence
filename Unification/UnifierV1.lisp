;;*****************************************************************************
;;  Unifier V1
;;  Adapted and Implemented with Peter Norvig's
;;  Paradigms of Artificial Intelligence Programming
;;*****************************************************************************
;;
;;Note: this is the first iteration, higher version numbers account
;;      for more bugs, errors, and functionallity


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
        ((variable-p x) (unify-variable x y bindings))
        ((variable-p y) (unify-variable y x bindings))
        ((eql x y) bindings)
        ((and (consp x) (consp y))
         (unify (rest x) (rest y)
           (unify (first x) (first y) bindings)))
        (t fail)))

(defun unify-variable (var x bindings)
  "Unify var with x, this uses and may update bindings"
  (if (get-binding var bindings)
      (unify (lookup var bindings) x bindings)
      (extend-bindings var x bindings)))

;;Bugs:
;;   Cannot currently handle binding to a variable which has previously been
;;   bound to itself.
;;    Example:
;;      Given (unify '(?x ?x a) '(?y ?y ?y))
;;      one would expect the following binds:
;;        ((?x . ?y) (?y . a))
;;      Instead, once (?x . ?y) is created, any call to find the value
;;      of ?x or ?y leads to an infinite loop attempting to look up a value.
;;
;;    Solution:
;;      Attempt to 
