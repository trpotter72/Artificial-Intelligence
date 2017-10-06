(defun find-goal-relevant-concept-seeds (goals &optional (concepts cltm*))
  ;; find non-primitive concepts that pertain to any goal in goals
  ;; Do not save any bindings.
  (loop for concept in concepts 
     when (and (concept-conditions concept) (concept-relates-to-goals concept goals))
     collect concept))
