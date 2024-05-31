(defmacro defun (name bindings)
  (list 'def name (cons 'lambda (cons bindings &rest))))

(defmacro let (bindings)
  (cons (cons 'lambda (cons (map car bindings) &rest))
        (map cadr bindings)))

(eval-when-compile
  (defun car (cons)
    (car cons))

  (defun cadr (cons)
    (car (cdr cons)))

  (defun map (fn list)
    (if (nil? list)
        nil
        (cons (fn (car list))
              (map fn (cdr list))))))

(defun and (a b)
  (if a (if b t nil) nil))

(defun or (a b)
  (if a t (if b t nil)))
