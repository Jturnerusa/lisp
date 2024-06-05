(defmacro progn ()
  (list (cons 'lambda (cons '() &rest))))

(defmacro let (bindings)
  (cons (cons 'lambda (cons (map car bindings) &rest))
        (map cadr bindings)))

(defmacro let* (bindings)
  (list (expand-let* bindings &rest)))

(eval-when-compile

  (def expand-let* (lambda (bindings body)
                     (if (nil? bindings)
                         (cons 'lambda (cons '() body))
                         (cons (list 'lambda (list (car (car bindings)))
                                     (expand-let* (cdr bindings) body))
                               (cdr (car bindings))))))
  
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

  (def do (lambda (fn list)
            (if (nil? list)
                nil
                (progn (fn (car list))
                       (do fn (cdr list))))))
 
  (def map (lambda (fn list)
             (if (nil? list)
                 nil
                 (cons (fn (car list))
                       (map fn (cdr list))))))

  (def fold (lambda (fn list)
              (let ((acc (car list)))
                (do (lambda (e)
                      (set acc (fn acc e)))
                    (cdr list))
                acc)))

  (def filter (lambda (pred list)
                (if (nil? list)
                    nil
                    (if (pred (car list))
                        (cons (car list) (filter pred (cdr list)))
                        (filter pred (cdr list))))))

  (def nth (lambda (list n)
             (if (nil? list)
                 nil
                 (if (= n 0)
                     (car list)
                     (nth (cdr list) (- n 1))))))

  (def length (lambda (list)
                (let ((loop (lambda (list counter loop)
                              (if (nil? list)
                                  counter
                                  (loop (cdr list) (+ counter 1) loop)))))
                  (loop list 0 loop))))

  (def and (lambda (a b)
             (if a
                 (if b
                     t nil)
                 nil)))

  (def or (lambda (a b)
            (if a
                t
                (if b
                    t nil))))

  (def last (lambda (list)
              (if (nil? list)
                  nil
                  (if (nil? (cdr list))
                      (car list)
                      (last (cdr list)))))))
