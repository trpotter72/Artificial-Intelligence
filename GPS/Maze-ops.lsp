;;Maze-op creation for GPSv2
;;Pass in values representitive of the connectivity of a maze
;;& create a list of ops to use in conjunction with GPSv2 to solve the maze

(defun make-maze-ops (pair)
  (list (make-maze-op (first pair) (nth 1 pair))
   (make-maze-op (nth 1 pair) (first pair))))

(defun make-maze-op (first second)
  "Makes an op for moving from first to second"
  (op `(from ,first to ,second)
    :preconds `((at ,first))
    :add-list `((at ,second))
    :del-list `((at ,first))))

(defun mappend (fn &rest lsts)
  "maps elements in list and finally appends all resulted lists."
  (apply #'append (apply #'mapcar fn lsts)))
