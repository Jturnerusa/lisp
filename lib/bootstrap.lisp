(defmacro defun (name bindings)
  (list 'def name (list 'lambda bindings (cons (list progn) &rest))))

(defun cadr (cons)
  (car (cdr cons)))

(defun not (p)
  (if p nil t))

(defun map (f list)
  ((lambda (f list acc)
     (progn (loop (not (nil? list))
             (progn (set acc (push-back acc (f (car list))))
                    (set list (cdr list))))
             acc))
   f list nil))

(defmacro let (bindings)
  (cons (list 'lambda (map car bindings)
              (cons 'progn &rest))
        (map cadr bindings)))
