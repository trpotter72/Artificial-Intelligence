;;General Problem Solver Version 2
;;By Trenton Potter
;;From Paradigms of Artificial Intelligence Programming by Peter Norvig

;Description
;;Solves problems given an initial state, goal state, and list of operators which modify states given preconditions
;;(attempts to over come some issues associated with v1

;Issues
;;


  ;;;Global Variables;;;

(defvar *ops* nil "List of available operators to GPS Program") ;; Changed durn

(defvar *dbg-ids* nil "List of identifiers currently being used by debugger")


  ;;;Data Types;;;

(defstruct op
  "Structure of an operator"
  (action nil) (preconds nil) (add-list nil) (del-list nil))


  ;;;Functions;;;

;;Debugging
(defun dbg-indent (id indent format-string &rest args)
  "print indented debugging info if (DEBUG ID) has been specified."
  (when (member id *dbg-ids*)
    (fresh-line *debug-io*)
    (dotimes (i indent) (princ "  " *debug-io*))
    (apply #'format *debug-io* format-string args)))

(defun debug (&rest ids)
  "Start dbg output on the given ids"
  (setf *dbg-ids* (union ids *dbg-ids*)))


;;Auxilary Functions
(defun executing-p (x)
  "Is x of the form: (executing ...)?"
  (starts-with x 'executing))

(defun starts-with (list x)
  "Is this a list AND is the list's first element x?"
  (and (consp list) (eql x (first list))))

(defun appropriate-p (goal op)
  "An op is appropriate to a goal if it is in its add-list."
  (member-equal goal (op-add-list op)))

(defun find-all (item sequence &rest keyword-args &key (test #'eql) test-not &allow-other-keys)
  "Find all elements of a sequence that match an item, according to the keywords.  Doesn't alter the sequence"
  (if test-not
    (apply #'remove item sequence :test-not (complement test-not) keyword-args)
    (apply #'remove item sequence :test (complement test) keyword-args)))

(defun member-equal (item list)
  (member item list :test #'equal))


;;Operators
(defun convert-op (op)
  "Make op conform to the (EXECUTING op) convention in v2" ;;mapc to create new op list from old ops
  (unless (some #'executing-p (op-add-list op))
    (push (list 'executing (op-action op)) (op-add-list op)))
  op)

(defun op (action &key preconds add-list del-list)
  "Make a new operator that obeys the (executing op) convention of v2"
  (convert-op
    (make-op :action action
      :preconds preconds
      :add-list add-list
      :del-list del-list)))

(defun use (oplist)
  "Use oplist as the default list of operators."
  ;; Return something useful, but not too verbose:
  ;; the number of operators.
  (length (setf *ops* oplist)))


;;Primary Functions
(defun GPS (state goals &optional(*ops* *ops*))
  "General Problem Solver: from state, achieve goals using ops."
  (remove-if #'atom (achieve-all (cons '(start) state) goals nil)))  ;;Formats out all non (START) or (EXECUTING ...) pieces from the current state
                                    ;;leaving output of steps taken to solve problem

(defun achieve-all (state goals goal-stack)
  "Achieve each goal AND make sure it holds at the end."
  (let ((current-state state))
    (if (and (every #'(lambda (g)  ;;If all goals are achieved & the goals have not been sibling clobbered return updated state
                       (setf current-state
                         (achieve current-state g goal-stack)))
              goals)
         (subsetp goals current-state :test #'equal))
      current-state)))

(defun achieve (state goal goal-stack)
  "A goal is achieved if it already holds, or if there is an appropriate op that is applicable."
  (dbg-indent :gps (length goal-stack) "Goal: ~a" goal)
  (cond ((member-equal goal state) state)  ;;If the goal is in the current state, return the state
    ((member-equal goal goal-stack) nil)  ;; If the goal is in the goal stack return nil (fixes recursive sub-goal problem)
    (t (some #'(lambda (op) (apply-op state goal op goal-stack)) ;;Otherwise attempts to apply an op
        (find-all goal *ops* :test #'appropriate-p)))))

(defun apply-op (state goal op goal-stack)
  "return a new, transformed state if op is applicable."
  (dbg-indent :gps (length goal-stack) "Consider: ~a" (op-action op))

  (let ((state2 (achieve-all state (op-preconds op)  ;;Attempt to achieve all preconds of the given op
                  (cons goal goal-stack))))  ;;Add current goal to goal stack
    (unless (null state2)
      (dbg-indent :gps (length goal-stack) "Action: ~a" (op-action op))
      (append (remove-if #'(lambda (x)
                            (member-equal x (op-del-list op)))  ;;Removes delete-list from current state
                state2)
          (op-add-list op)))))  ;;Adds the add-list


;;Testing
(defparameter *school-ops*
  (list
    (op  'drive-son-to-school
         :preconds '(son-at-home car-works)
         :add-list '(son-at-school)
         :del-list '(son-at-home))
    (op  'shop-installs-battery
         :preconds '(car-needs-battery shop-knows-problem shop-has-money)
         :add-list '(car-works))
    (op  'tell-shop-problem
         :preconds '(in-communication-with-shop)
         :add-list '(shop-knows-problem))
    (op  'telephone-shop
         :preconds '(know-phone-number)
         :add-list '(in-communication-with-shop))
    (op  'look-up-number
         :preconds '(have-phone-book)
         :add-list '(know-phone-number))
    (op  'give-shop-money
         :preconds '(have-money)
         :add-list '(shop-has-money)
         :del-list '(have-money))))
