(defparameter david-plan* '((open ?o)
			    (open ?o)
			    (open ?o)
			    (look-right ?robot)))
(defparameter boxes* '(BX0 BX1 BX2 BX3 BX4 BX5 BX6))
(create-concepts

 ;;primitive concepts
 ((on ^id ?o1 ?o2 ^height ?height)
  :elements ((block ^id ?o1 ^x ?x1 ^y ?y1 ^len ?len1 ^height ?height1)
	     (block ^id ?o2 ^x ?x2 ^y ?y2 ^len ?len2 ^height ?height2))
  :tests ((*overlapping ?x1 ?len1 ?x2 ?len2)
	  (= ?y1 (+ ?y2 ?height2)))
  :binds (?height (+ ?height1 ?height2)))

 ((on-table ^id ?o1 ?o2)
  :elements ((block ^id ?o1 ^x ?x1 ^y ?y1 ^len ?len1)
	     (table ^id ?o2 ^x ?x2 ^y ?y2 ^len ?len2))
  :tests ((*overlapping ?x1 ?len1 ?x2 ?len2)
	  (= ?y1 ?y2)))

 ((in ^id ?o1 ?o2)
  :elements ((block ^id ?o1 ^x ?x1 ^len ?len1 ^height ?height1)
	     (box ^id ?o2 ^x ?x2 ^len ?len2 ^height ?height2 ^closed ?closed))
  :tests ((*overlapping ?x1 ?len1 ?x2 ?len2)
	  (>= ?height2 ?height1)
	  (not (eq 'yes ?closed))))

 ((clear ^id ?block)
  :elements ((block ^id ?block)
	     (not (on ?another ?block))))

 ;;Assume the length of any block is not greater than ?len
 ((occupied-area ^id ?sx)
  :elements ((x-section ^id ?sx ^len ?len)
	     (block ^id ?o ^x ?x ^len ?l))
  :tests ((*overlapping ?sx ?len ?x ?l)))

 )

(defun *overlapping (x1 len1 x2 len2)
  (if (and (numberp x1)
	   (numberp len1)
	   (numberp x2)
	   (numberp len2))
      (or (and (<= x1 x2)
	       (>= (+ x1 len1) x2))
	  (and (<= x2 x1)
	       (>= (+ x2 len2) x1)))))

(defun *near (x1 x2)
  (if (and (numberp x1)
	   (numberp x2))
      (<= (abs (- x1 x2)) *step)))

(setf *step 1)
(setf state0*
      '((robot ^id R0 ^looking left ^holding nothing)
	(box ^id Bx0 ^x 2 ^y 0 ^len 3 ^closed yes ^color green ^height 3)
	(box ^id Bx1 ^x 4 ^y 0 ^len 3 ^closed yes ^color red ^height 3)
	(block ^id B1 ^x 2 ^y 0 ^len 2 ^height 2)
	(block ^id B2 ^x 30 ^y 0 ^len 2 ^height 2)
	(table ^id Rainbow ^x 0 ^y 0 ^len 20)
	(table ^id Cloud ^x 21 ^y 0 ^len 20)))

(setf state0* (create-cinstances-for-percepts state0*))

#|
(create-skills
 ((open ?o)
  :elements (?o is (box ?o ^x ?x ^y ?y ^len ?l ^closed ?closed ^height ?height))
  :conditions ((eq ?closed 'yes)
	       (not (eq ?close 'no)))
  :actions ((*open ?o))
  :effects (?o is (box ?o ^x ?x ^y ?y ^len ?l ^closed no ^color ?color ^height ?height)
	       (in ?object ?o)))

 ((close ?o)
  :elements (?robot is (robot ?robot ^looking ?looking ^holding ?holding)
		    ?o is (box ?o ^x ?x ^y ?y ^len ?l ^closed ?closed ^height ?height))
  :conditions ((eq ?closed 'no)
	       (not (eq ?closed 'yes)))
  :actions ((*close ?o))
  :effects (?robot is (robot ?robot ^looking ?looking ^holding ?holding)
		   ?o is (box ?o ^x ?x ^y ?y ^len ?l ^closed yes ^color ?color ^height ?height)))
 ((look-right ?robot)
  :elements (?robot is (robot ?robot ^looking ?looking ^holding ?holding))
  :conditions ((not (eq ?looking 'right)))
  :actions ((*look-right ?robot))
  :effects (?robot is (robot ?robot ^looking right ^holding ?holding)))

 ((look-left ?robot)
  :elements (?robot is (robot ?robot ^looking ?looking ^holding ?holding))
  :conditions ((not (eq ?looking 'left)))
  :actions ((*look-left ?robot))
  :effects (?robot is (robot ?robot ^looking left ^holding ?holding)))

 ((pick-up ?o)
  :elements (?robot is (robot ?robot ^looking ?looking ^holding nothing)
		    ?o is (block ?o ^x ?x ^y ?y ^len ?l ^height ?h))
  :conditions ((clear ?o))
  :actions ((*pick-up ?robot ?o))
  :effects (?robot is (robot ?robot ^looking ?looking ^holding ?o)
		   ?o is (block ?o ^x unknown ^y unknown ^len ?l ^height ?h)))

 ;Stack with left alignment
 ((stack ?o1 ?o2)
  :elements (?o1 is (block ?o1 ^x ?x1 ^y ?y1 ^len ?l1 ^height ?h1)
		 ?o2 is (block ?o2 ^x ?x2 ^y ?y2 ^len ?l2 ^height ?h2)
		 ?robot is (robot ?robot ^looking ?looking ^holding ?o1))
  :conditions ((clear ?o2))
  :actions ((*stack ?robot ?o1 ?o2))
  :effects (?o1 is (block ?o1 ^x ?x2 ^y (+ ?y2 ?h2) ^len ?l1 ^height ?h1)
		(on ?o1 ?o2)
		?robot is (robot ?robot ^looking ?looking ^holding nothing))
  :tests ((numberp ?y2)))

 ((put-down ?robot ?o ^x ?x)
  :elements (?robot is (robot ?robot ^looking ?looking ^holding ?o)
		    ?o is (block ?o ^x ?x1 ^y ?y1 ^len ?l ^height ?h))
					;we assume that the region [?x, (+ ?x ?length)] is clear
  :conditions ((x-section ?x ?len)
               (not (occupied-area ?x)))
  :actions ((*put-down ?robot ?o ?x))
  :effects (?o is (block ?o ^x ?x ^y 0 ^len ?l ^height ?h)
	       ?robot is (robot ?robot ^looking ?looking ^holding nothing))
  :tests ((<= ?l ?len))))

(defun initialize-world ()
  (create-problems ((on B1 B2)))
  nil)

(defun *look-right (object)
  (let ((robot (car (member object state0* :key 'second :test 'equal))))
    (setf (cadr (member '^looking robot :test 'equal)) 'right)))

(defun *look-left (object)
  (let ((robot (car (member object state0* :key 'second :test 'equal))))
    (setf (cadr (member '^looking robot :test 'equal)) 'left)))

(defun *open (object)
  (format t "Executing *OPEN ~s" object)
  (let ((box (car (member object state0* :key 'second :test 'equal))))
    (setf (cadr (member '^closed box :test 'equal)) 'no)))

(defun *close (object)
  (let ((box (car (member object state0* :key 'second :test 'equal))))
    (setf (cadr (member '^closed box :test 'equal)) 'yes)))

(defun *pick-up (subject object)
  (let ((robot (car (member subject state0* :key 'second :test 'equal)))
	(block (car (member object state0* :key 'second :test 'equal))))
    (setf (cadr (member '^holding robot :test 'equal)) object)
    (setf (cadr (member '^x block :test 'equal)) 'unknown)
    (setf (cadr (member '^y block :test 'equal)) 'unknown)))

(defun *stack (subject object1 object2)
  (let ((robot (car (member subject state0* :key 'second :test 'equal)))
	(block (car (member object1 state0* :key 'second :test 'equal)))
	(location (car (member object2 state0* :key 'second :test 'equal))))
    (setf (cadr (member '^holding robot :test 'equal)) 'nothing)
    (setf (cadr (member '^x block :test 'equal))
	  (cadr (member '^x location :test 'equal)))
    (setf (cadr (member '^y block :test 'equal))
	  (+ (cadr (member '^y location :test 'equal))
	     (cadr (member '^height location :test 'equal))))))

(defun *put-down (subject object x)
  (let ((robot (car (member subject state0* :key 'second :test 'equal)))
	(block (car (member object state0* :key 'second :test 'equal))))
    (setf (cadr (member '^holding robot :test 'equal)) 'nothing)
    (setf (cadr (member '^x block :test 'equal)) x)
    (setf (cadr (member '^y block :test 'equal)) 0)))
|#

(defun preattend ()
  ;(format t "~%~%State:~%~S~%~%" state0*)
  (let* ((robot (car (member 'robot state0* :key 'first :test 'equal)))
	 (looking (cadr (member '^looking robot :test 'equal)))
	 (state (remove 'robot state0* :key 'first :test 'equal))
	 (blocks (remove 'nil (loop for x in state collecting
				   (if (eq (first x) 'block)
				       x))))
	 (boxes (remove 'nil (loop for x in state collecting
				   (if (eq (first x) 'box)
				       x)))))
    (if (eq looking 'left)
	(setq pstm* (append (remove-if #'(lambda (x)
			       (or (> (cadr (member '^x x :test 'equal)) 20)
				   (and (member x blocks :test 'equal)
					(some #'(lambda (z)
						  (not (null z)))
					      (mapcar #'(lambda (box)
							  (let ((x1 (cadr (member '^x x :test 'equal)))
								(x2 (cadr (member '^x box :test 'equal)))
								(len1 (cadr (member '^len x :test 'equal)))
								(len2 (cadr (member '^len box :test 'equal)))
								(closed (cadr (member '^closed box :test 'equal))))
							    (and (*overlapping x1 len1 x2 len2)
								 (eq 'yes closed))))
						      boxes)))))
				       state)
			    (list robot)))
	(setq pstm* (append (remove-if #'(lambda (x)
			       (or (< (cadr (member '^x x :test 'equal)) 20)
				   (and (member x blocks :test 'equal)
					(some #'(lambda (z)
						  (not (null z)))
					      (mapcar #'(lambda (box)
							  (let ((x1 (cadr (member '^x x :test 'equal)))
								(x2 (cadr (member '^x box :test 'equal)))
								(len1 (cadr (member '^len x :test 'equal)))
								(len2 (cadr (member '^len box :test 'equal)))
								(closed (cadr (member '^closed box :test 'equal))))
							    (and (*overlapping x1 len1 x2 len2)
								 (eq 'yes closed))))
						      boxes)))))
				       state)
			    (list robot))))))

(defun update-world ())
