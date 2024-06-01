(defmacro let (bindings)
  (cons (cons 'lambda (cons (map car bindings) &rest))
        (map cadr bindings)))

(eval-when-compile
  (def car (lambda (cons)
             (car cons)))

  (def cadr (lambda (cons)
              (car (cdr cons))))

  (def map (lambda (fn list)
             (if (nil? list)
                 nil
                 (cons (fn (car list))
                       (map fn (cdr list))))))

  (def and (lambda (a b)
             (if a
                 (if b
                     t nil)
                 nil)))

  (def or (lambda (a b)
            (if a
                t
                (if b
                    t nil)))))
