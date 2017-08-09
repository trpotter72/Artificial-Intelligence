(defun minimax (board depth player)
  "Finds the best move using eval fn and recursive calls to minimax"
  (cond ((deep-enough board depth)
         (list (score board player)))
        (t
          (let ((next-moves (possible-moves board player))
                (best-move nil)
                (best-score -99999))
            (cond ((null next-moves)
                   (list (score board player)))
                  (t
                    (loop for move in next-moves do
                      (let* ((best-child (minimax move (1+ depth) (opposite player)))
                             (new-value (- (car best-child))))
                            (when (> new-value best-score)
                              (setq best-score new-value)
                              (setq best-move move))))
                   (cons best-score best-move)))))))




(defun deep-enough (pos depth)
  (declare (ignore depth))
  (or (win? pos 1)
      (win? pos -1)
      (draw? pos)))

(defun play (&optional machine-first)
  "Starts game with play-bot"
  (let ((board *board*)
        (next nil))
       (when machine-first
         (setq board (rest (minimax board 0 -1))))
       (do  ()
            ((or
              (win? board 1)
              (win? board -1)
              (draw? board))
             (format t "Final position: ~%")
             (print-board board)
             (cond
               ((win? board -1) (format t "I win.~%"))
               ((win? board 1) (format t "You win.~%"))
               (t (format t "Draw.~%"))))
            (print-board board)
            (format t "Your move: ")
            (let ((move (read)))
              (loop until (setq next (mark-board board 1 move))
                do (format t "~%~a Illegal! Try again: " move)
                (setq move (read)))
              (setq board next))
            (when (and (not (draw? board))
                       (not (win? board -1))
                       (not (win? board 1)))
              (print-board board)
              (setq board (rest (minimax board 0 -1)))
              (if (and (not (draw? board))
                       (not (win? board -1)))
                (format t "My move: ~%"))))))
