;;Tic Tac Toe Game
;;Developed by Trenton Potter

;;Functions
;add-mark (x/o y-pos x-pos)
;winner ()
;


(defparameter *board*
  '(nil nil nil
    nil nil nil
    nil nil nil)
  "Describes the current board state")

(defun print-board (board)
  "prints board in 2d representation"
  (format t "~% ~d ~d ~d ~% ~d ~d ~d ~% ~d ~d ~d ~%~%"
    (or (nth 0 board) ".") (or (nth 1 board) ".") (or (nth 2 board) ".")
    (or (nth 3 board) ".") (or (nth 4 board) ".") (or (nth 5 board) ".")
    (or (nth 6 board) ".") (or (nth 7 board) ".") (or (nth 8 board) ".")))
(defparameter *whose-turn*
  1
  "Describes whether player 1 or -1's turn")
(defun switch-turns ()
  "Switches turns from one player to the other"
  (setf *whose-turn* (* *whose-turn* -1)))

(defun mark-board (y x)
  "Places a mark on the board at given y & x, checks to see if occupuied and in bounds"
  (if (and (>= x 0) (>= y 0) (<= x 2) (<= y 2))
    (if (not (elt *board* (+ x (* y 3))))
        (progn
          (setf (elt *board* (+ x (* y 3))) *whose-turn*)
          (switch-turns)
          t))
    nil))

(defun winner (player)
  "Checks checks if player won 1, cats game 0, or neither nil"
  (or
    (and
      (eql player (nth 0 *board*))
      (eql player (nth 1 *board*))
      (eql player (nth 2 *board*)))
    (and
      (eql player (nth 0 *board*))
      (eql player (nth 3 *board*))
      (eql player (nth 6 *board*)))
    (and
      (eql player (nth 0 *board*))
      (eql player (nth 4 *board*))
      (eql player (nth 8 *board*)))
    (and
      (eql player (nth 1 *board*))
      (eql player (nth 4 *board*))
      (eql player (nth 7 *board*)))
    (and
      (eql player (nth 2 *board*))
      (eql player (nth 5 *board*))
      (eql player (nth 8 *board*)))
    (and
      (eql player (nth 2 *board*))
      (eql player (nth 4 *board*))
      (eql player (nth 6 *board*)))
    (and
      (eql player (nth 3 *board*))
      (eql player (nth 4 *board*))
      (eql player (nth 5 *board*)))
    (and
      (eql player (nth 6 *board*))
      (eql player (nth 7 *board*))
      (eql player (nth 8 *board*)))))
