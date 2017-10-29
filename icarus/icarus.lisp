(load "memories")
(load "compiler")
(load "matcher")
;(load "postprocessor")
;(load "newinterpreter")

; Dan's problem solver
(load "Unification")                    ; unification code adapted from Norvig
;(load "solver-utilities")               ; macros, support for weighted skill selection heuristics
;(load "failure-contexts")               ; failure recording and retrieval for problem solving
;(load "operator-match")                 ; maximal matches of skills and concepts against goals and beliefs
;(load "beliefs")                        ; concept matching against  beliefs
;(load "problem-solver")                 ; core bits of problem solver (dgs revision 03/2012)
;(load "solver-rewrite")			; main routines for rewritten solver
;(load "solver-rewrite-patch")
;(load "one-step-lookahead")             ; lookahead plus deductive closure on effects of a skill

; David's patches
;(load "solver-rewrite-patch")
;(load "newmatcher-patch")
; David's episodic module
;(load "episodic")

; Son's planner
;(load "planning")

;(infer cltm* pstm* cstm*)

;(setf cltm* nil cstm* nil sltm* nil)

;(load "Domains/Staircase/staircase")
;(load "Domains/Staircase/staircase-connect")
;(load "Domains/Staircase/bridge")
;(load "Domains/Blocksworld/Block-same-color")
;(load "Domains/SimpleMineCraft/SimpleMC")
;(load "Domains/Malmo/simple-zombie")
;(load "Domains/Malmo/grand-challenge")
(load "Block-Episodic")
;(load "Domains/Lab/LabWorld/LabObserver")
;(load "Domains/Wellworld/wellworld")
;(setq problem-solver-enabled* 'planner)
;(setq problem-solver-enabled* 'meansends)
;(setf  cstm* (infer cltm* pstm* cstm*))

;(setf gstm* '((on b1 b2)))
