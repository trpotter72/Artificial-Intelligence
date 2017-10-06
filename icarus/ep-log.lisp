#| Episodic Logger |#
(defvar log-path* (merge-pathnames "log.txt"))
(defvar log-insert* nil)
(defvar log-generalize* nil)
#| Write a message to the log file |#

;; message = list of format arguments
(defun log-message (message)
  (with-open-file (log log-path*
		       :direction :output
		       :if-exists :append
		       :if-does-not-exist :create)
    (apply #'format (cons log message))))

#| Turn on logging flags |#

(defun enable-logging ()
  (delete-log)
  (setq log-insert* t)
  (setq log-generalize* t))

(defun disable-logging ()
  (setq log-insert* nil)
  (setq log-generalize* nil))

(defun get-log-variables ()
  (format t "Log Insert: ~S~%Log Generalize: ~S~%" log-insert* log-generalize*))

#| Delete the log file |#

(defun delete-log ()
  (sb-ext:run-program "rm" (list (namestring log-path*)) :search t :wait t))
