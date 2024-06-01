(defmacro let (bindings)
  (cons (cons 'lambda (cons (map car bindings) &rest))
        (map cadr bindings)))

(eval-when-compile
  
  ;; Some primitive operations like car, cdr, cons, etc are implemented
  ;; as special operations in the compiler and aren't bound to a symbol
  ;; as functions. This makes (map car (list (cons 'a 'b))) for example
  ;; not work, so we create some functions with the same name as builtins
  ;; that just call the builtin internally.

  ;; These functions also should be available at compile time so they can
  ;; be used in macros;
  
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
