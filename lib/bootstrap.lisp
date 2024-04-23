(defmacro defun (name bindings)
  (list 'def name (list 'lambda bindings (cons (list progn) &rest))))

(defun cadr (cons)
  (car (cdr cons)))

(defun not (p)
  (if p nil t))

(defun map (f list)
  (if (nil? list)
      nil
      (cons (f (car list))
            (map f (cdr list)))))

(defmacro let (bindings)
  (cons (list 'lambda (map car bindings)
              (cons 'progn &rest))
        (map cadr bindings)))
