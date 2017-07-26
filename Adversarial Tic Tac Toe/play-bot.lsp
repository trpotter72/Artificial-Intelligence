(defun get_best (func lst)
  "Returns the best using func"
  (let
    ((best_val (funcall func (first lst)))
     (best_item (first lst)))
    (loop for item in (rest lst)
      do
        (if (< best_val (funcall func item))
          (progn
            (setf best_val (funcall func item))
            (setf best_item item))
          nil
          ))
    best_item))


(defun give_score (x)
  "Gives an arbitrary score to a value (used for testing)"
  (+ x 5))
