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
  (case x
    ('a 5)
    ('b 2)
    ('f 1)
    (otherwise 0)))

(defconstant *win-lines*
  '((0 1 2)
    (0 3 6)
    (0 4 8)
    (1 4 7)
    (2 5 8)
    (2 4 6)
    (3 4 5)
    (6 7 8)))

(defun board-score (brd player)
  "Given a board, returns a score based on player positioning"
  (let ((score 0))
    (loop for line in *win-lines* do
      (incf score (line-score brd player line))
      (decf score (opponent-line-score brd player line)))
    score))

(defun line-score (brd player line)
  "Given a board, it evaluates the given line for a score"
  (let ((sample (list (nth (first line) brd)
                      (nth (second line) brd)
                      (nth (third line) brd))))
    (if (member (opposite player) sample)
      (return-from line-score 0)
      (if (member player sample)
        (if (member player (rest (member player sample)))
          (if (member player (rest (member player (rest (member player sample)))))
            (return-from line-score 999999)
            (return-from line-score 5000))
          (return-from line-score 1000))
        0))))

(defun opponent-line-score (brd player line)
  "Given a board, it evaluates the given line for a score"
  (let ((sample (list (nth (first line) brd)
                      (nth (second line) brd)
                      (nth (third line) brd))))
    (if (member (player) sample)
      (return-from line-score 0)
      (if (member (opposite player) sample)
        (if (member (opposite player) (rest (member opposite player sample)))
          (return-from line-score 500000)
          (return-from line-score 1000))
        0))))

(defun opposite (player)
  "returns the opposite player from the given"
  (* -1 player))
