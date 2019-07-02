(defun g (n) (dotimes (i n) (print i)))

(defun f (x)
  (+ 4000 (if (= x 1) (progn (let ((z x)) (print z) (setq z 1))) x)))
