;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; beliefs.lisp
;;   primitives for matching onto belief memory (cstm*)
;;;;;;;;;;;;



(defun  match-positive-condition (condition elist bindings &key (find-first nil))
  ;; Finds all ways to match condition (an sexpr) on elist (a list of concept structures) given bindings.  
  ;; If find-first = T, returns the first match found, otherwise returns all matches found.
  ;; Refuses to bind the same object to two different variables.

  ;; Returns result in icarus binding format, as it supports multiple binding sets: icarus-fail =
  ;; (nil), icarus-no-bindings = (T), else a list of binding sets Any bindingset returned includes
  ;; the input bindings.

  (let ((all-bindings nil)
	(exact-match nil))
    (loop for element in elist do

	(let* ((match (unify-with-belief condition element bindings)))

	  (cond ((and (has-norvig-bindings match) find-first) 
		 (return (create-icarus-binding :binding-env (norvig-bindings match))))
		((and (equal match no-bindings) find-first) (return icarus-no-bindings))
		((has-norvig-bindings match) (push (norvig-bindings match) all-bindings))
		((equal match no-bindings) (setq exact-match t))))
       finally (return
		 (cond (all-bindings (create-icarus-binding :binding-env-list all-bindings))
		     (exact-match icarus-no-bindings)
		     (t icarus-fail))))))

(defun unify-with-belief (condition element bindings)
  ;; element is a cinstance from belief memory
  (let ((clause (cinstance-head element)))
    (if bindings 
	(unify condition clause bindings)
	(unify condition clause))))


(defun create-icarus-binding (&key binding-env binding-env-list)
  ;; icarus bindings are of the form  icarus-fail = (nil),  icarus-no-bindings = (T), or ( binding-env+ )
  (cond (binding-env (list binding-env))
	(binding-env-list binding-env-list)
	(t icarus-fail)))

(defun match-negative-condition (condition elist bindings &aux res)
  ;; finds the first way to match condition on elist given bindings
  ;; ASSUMES condition is of the form (NOT <x>)
  ;; returns icarus-no-bindings if the (not <x>) is true, else icarus-fail

  (setq res (match-positive-condition (cadr condition) elist bindings :find-first t))
  (icarus-binding-negation res))

(defun match-condition (condition elist bindings)
  (if (negative-clause condition) 
      (match-negative-condition condition elist bindings)
      (match-positive-condition condition elist bindings)))

(defun icarus-binding-negation (icarus-binding)
  ;; transform icarus-fail into a success but with no stored bindings
  ;; transform an icarus positive result of any form into icarus-fail
  (if (equal icarus-binding icarus-fail) 
      icarus-no-bindings
      icarus-fail))
