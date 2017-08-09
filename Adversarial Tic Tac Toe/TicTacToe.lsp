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

(defconstant *win-lines*
  '((0 1 2)
    (0 3 6)
    (0 4 8)
    (1 4 7)
    (2 5 8)
    (2 4 6)
    (3 4 5)
    (6 7 8)))

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
  (setf *whose-turn* (opposite *whose-turn*)))

(defun opposite (player)
  "returns the opposite player from the given"
  (* -1 player))

(defun mark-board (board player move)
  "Places a mark on the board at given y & x, checks to see if occupuied and in bounds"
  (unless (nth move board)
    (let ((new-board (copy-list board)))
      (setf (nth move new-board) player)
      new-board)))

(defun possible-moves (board player)
  "List of boards possible for a player"
  (loop for m from 0 to 8
    unless (nth m board)
    collect (mark-board board player m)))

(defun score (board player)
  "Returns a score for a board if a player has one or lost"
  (cond ((win? board player)
         '10)
        ((win? board (opposite player))
         '-10)
        (t
         '0)))

(defun win? (board player)
  "Checks checks if player won"
  (or
    (and
      (eql player (nth 0 board))
      (eql player (nth 1 board))
      (eql player (nth 2 board)))
    (and
      (eql player (nth 0 board))
      (eql player (nth 3 board))
      (eql player (nth 6 board)))
    (and
      (eql player (nth 0 board))
      (eql player (nth 4 board))
      (eql player (nth 8 board)))
    (and
      (eql player (nth 1 board))
      (eql player (nth 4 board))
      (eql player (nth 7 board)))
    (and
      (eql player (nth 2 board))
      (eql player (nth 5 board))
      (eql player (nth 8 board)))
    (and
      (eql player (nth 2 board))
      (eql player (nth 4 board))
      (eql player (nth 6 board)))
    (and
      (eql player (nth 3 board))
      (eql player (nth 4 board))
      (eql player (nth 5 board)))
    (and
      (eql player (nth 6 board))
      (eql player (nth 7 board))
      (eql player (nth 8 board)))))

(defun draw? (board)
  "Checks to see if the board is a draw"
  (notany #'null board))
