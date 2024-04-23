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

(defun filter (p list)
  (let ((acc nil))
    (map (lambda (e)
           (if (p e)
               (set acc (push-back acc e))
               nil))
         list)
    acc))

(defun fold (f list)
  (let ((acc (car list)))
    (map (lambda (e)
           (set acc (f acc e)))
         (cdr list))
    acc))
