(defmacro progn ()
  (progn-expand &rest))

(defmacro defun (name bindings)
  (list 'def name (list 'lambda bindings (cons 'progn &rest))))

(defmacro let (bindings)
  (cons (list 'lambda (map car bindings)
              (cons 'progn &rest))
        (map cadr bindings)))

(def progn-expand (lambda (exprs)
                    (if (nil? (cdr exprs))
                        (car exprs)
                        (list (list 'lambda (list 'x) (if (nil? (cdr exprs))
                                                          (car exprs)
                                                          (progn-expand (cdr exprs))))
                              (car exprs)))))

(defun not (p)
  (if p nil t))

(defun cadr (cons)
  (car (cdr cons)))

(defun do (f list)
  (if (nil? list)
      nil
      (progn (f (car list))
             (do f (cdr list)))))

(defun map (f list)
  (if (nil? list)
      nil
      (cons (f (car list))
            (map f (cdr list)))))

(defun filter (p list)
  (let ((acc nil))
    (do (lambda (e)
           (if (p e)
               (set acc (push-back acc e))
               nil))
         list)
    acc))

(defun fold (f list)
  (let ((acc (car list)))
    (do (lambda (e)
           (set acc (f acc e)))
         (cdr list))
    acc))
