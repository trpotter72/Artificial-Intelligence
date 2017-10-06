;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Failure-context functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Failure contexts record commitments made during problem solving that did not work out, and should
;; not be repeated.  These commitments can be very specific, or general.  For example: an intention
;; with bindings for a problem with bindings can fail because it will undo achieved goals, a problem
;; with bindings can fail because no operator can reduce it, and a problem without bindings can fail
;; because some objective must already be true in the world (and isn't).

;; The failure context mechanism utilizes this generality by storing the least specific cause
;; (commitments) at the time of failure, and treating known failures as partial specifications for
;; purposes of retrieval.  As a result, a problem with bindings that no operator could reduce
;; matches onto the same problem with any extension of those same bindings.

;; Failure contexts are stored by problem, so the problem (and the world state) are assumed constant
;; for all comparisons.

(defparameter empty* 'empty*) ;; used to distinguish an empty field from an empty binding set

(defstruct failure-context 
  (bindings empty*)     ;; bindings that caused the failure
  focus        ;; focus that caused the failure
  intention    ;; intention that caused the failure

  (problem-bindings empty*)   ;; bindings associated with a problem
  operator           ;; operator (concept or skill) 
  (operator-bindings empty*)  ;; bindings associated with an operator for the problem

  )

(defun print-failure-context (fc) 
  (let ((fb (failure-context-problem-bindings fc))
	(fop (failure-context-operator fc))
	(fopb (failure-context-operator-bindings fc)))

  (unless (eq fb empty*) (format t "~&   Problem bindings ~A" fb))
  (if fop (format t "~&   Operator ~A" fop))
  (unless (eq fb empty*) (format t "~&   Operator bindings ~A" fopb))))


;;;; failure recording functions
(defun fail-bindings-for-problem (problem) (fail-problem-bindings (problem-bindings problem) problem))

(defun fail-problem-bindings (bindings &optional (problem active-problem*))
  (create-and-store-failure-context 
   problem
   :problem-bindings bindings))

(defun fail-intention (intention &optional (problem (intention-problem-parent intention)))
  (create-and-store-failure-context 
   problem
   :intention intention
   :problem-bindings (problem-bindings problem)
   :operator (intention-operator intention)
   :operator-bindings (intention-bindings intention))

  (format t "~&Failing intention ~A for problem ~A" (intention-head intention) (problem-objectives problem))
  (setf (problem-intention problem) nil))

(defun create-and-store-failure-context (problem &rest keyargs)
  (let ((fc-instance (apply #'make-failure-context keyargs)))
    (push fc-instance (problem-failure-context-list problem))))

;;; failure context lookup functions
(defun match-failed-intention (problem intention)
  (member-failure-context-list? problem
				:operator (intention-operator intention)
				:operator-bindings (intention-bindings intention)))

(defun match-failed-operator (problem operator bindings)
  (member-failure-context-list? problem :operator operator :operator-bindings bindings))

(defun match-failed-bindings (problem bindings)
  (member-failure-context-list? problem	:problem-bindings bindings))

(defun matching-failure-contexts (new stored)
  ;; The matching mechanism treats known failures as partial specifications for purposes of
  ;; retrieval, in the sense that every non-empty field in a failure record must be a subset of the
  ;; corresponding field in the input.

  (let ((sb (failure-context-problem-bindings stored))
	(sop (failure-context-operator stored))
	(sopb (failure-context-operator-bindings stored))
	(nb (failure-context-problem-bindings new))
	(nop (failure-context-operator stored))
	(nopb (failure-context-operator-bindings stored)))

    ;; map empty* new bindings into nil for purposes of retrieval
    (if (eq nb empty*) (setq nb nil))
    (if (eq nopb empty*) (setq nopb nil))

    (and
     (if (eq sb empty*) t (bindings-subset sb nb))
     (if (null sop) t (eq sop nop))  ;; operators must represent the exact same concept or skill
     (if (eq sopb empty*) t (bindings-subset sopb nopb)))))


(defun member-in-failure-contexts (obj fclist &aux res)
  (loop for fc in fclist
       when (matching-failure-contexts obj fc) return fc))

(defun member-failure-context-list? (problem &rest keyargs)
  (let* ((query (apply #'make-failure-context keyargs))
	 (res (member-in-failure-contexts query (problem-failure-context-list problem))))
    (when res 
      (format t "~&The failure context ~A" res)
      (format t "~&matches the query")
      (print-failure-context query)
    res)))

(defun bindings-subset (sub whole)
  ;; returns true when every variable in sub that has a chained binding (not to a variable) has the
  ;; same chained value in whole

  (loop for pair in sub
       for var = (car pair)
       for final-binding = (get-chained-binding var sub)
       when (and final-binding (not (equal final-binding (get-chained-binding var whole)))) return nil
       finally (return t))) 

(defun get-chained-binding (var bindings &aux res)
 (setq res (get-final-binding var bindings))
 (if res (cons var (cdr res))))




