;; MEMORIES.LISP
;;  for ICARUS 2017
;;  written by Dongkyu Choi

;; MEMORIES:
;;
;; LONG-TERM MEMORIES
;;   CLTM*: Conceptual long-term memory
;;   SLTM*: Skill long-term memory
;;   GLTM*: Goal long-term memory
;;
;; SHORT-TERM MEMORIES
;;   CSTM*: Conceptual short-term memory
;;   GSTM*: Goal/intention short-term memory

;; REPRESENTATION:
;;
;;   Percepts:
;;     (<type> ^id <name> <attribute-value pairs>)
;;
;;   Concepts:
;;     ((<name> ^id <arguments> <attribute-value pairs>)
;;      :elements   (<percept or instantiated concept head>
;;                   ...)
;;      :tests      (<LISP function>
;;                   ...)
;;      :binds      (<var> <LISP function>
;;                   ...)
;;     )
;;
;;   Skills:
;;     ((<name> <arguments>)
;;      :elements   (<percept or instantiated concept head>
;;                   ...)
;;      :tests      (<LISP function>
;;                   ...)
;;      :actions    (<LISP function>
;;                   ...)
;;      :subskills  (<head>
;;                   ...)
;;      :changes    (<percept or instantiated concept head>
;;                   ...)
;;      :effects    (<percept or instantiated concept head>
;;                   ...)
;;     )
;;
;;   Long-term goals:
;;     (<name>
;;      :goal      <concept head>
;;      :relevance (<concept head>
;;                  ...)
;;     )

;****************************************************************************
; ICARUS Memories and Other Global Variables
;****************************************************************************
(defvar cltm* nil)
(defvar sltm* nil)
(defvar gltm* nil)

(defvar cstm* nil)
(defvar gstm* nil)

(defvar concepts* nil)
(defvar primitive-concepts* nil)
(defvar id-count* 0)

;****************************************************************************
; Initialization Functions
;****************************************************************************
(defun clear-concepts ()
  (setq cltm* nil)
  (setq concepts* nil)
  (setq primitive-concepts* nil))

(defun clear-skills ()
  (setq sltm* nil))

(defun clear-lt-goals ()
  (setq gltm* nil))

(defun clear-goals ()
  (setq gstm* nil))

(defun reset-id-count ()
  (setq id-count* 0))

(defun clear ()
  (clear-concepts)
  (if (equal inference* 'fast) (clear-fast-matcher))
  (clear-skills)
  (clear-lt-goals)
  (clear-goals)
  (reset-id-count)
  t)

;****************************************************************************
; Structural Definitions and their Support Functions
;****************************************************************************
(defstruct concept
  head id elements tests binds
  ;pivot threshold
  ;value duration expected pschildren ngchildren siblings
  ;instances rmdup attributes calculates counters
  )

(defstruct cinstance
  head id bindings subgoals 
  (degmatch 1.0) (timestamp cycle*) pos-dependencies
  neg-dependencies percepts total-percepts probability
  (time-stamps (cons nil 'NOW)) derived-object)

(defstruct skill
  head				
  id 
  elements
  tests
  actions
  subskills
  changes
  effects
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
