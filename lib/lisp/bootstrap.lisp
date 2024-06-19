  ;; Some primitive operations like car, cdr, cons, etc are implemented
  ;; as special operations in the compiler and aren't bound to a symbol
  ;; as functions. This makes (map car (list (cons 'a 'b))) for example
  ;; not work, so we create some functions with the same name as builtins
  ;; that just call the builtin internally.

  ;; These functions also should be available at compile time so they can
  ;; be used in macros;

(eval-when-compile
  (def car (lambda (cons)
             (car cons)))

  (def + (lambda (a b)
           (+ a b)))

  (def cadr (lambda (cons)
              (car (cdr cons))))

  (def caar (lambda (cons)
              (car (car cons))))

  (def cddr (lambda (cons)
              (cdr (cdr cons))))

  (def cdar (lambda (cons)
              (cdr (car cons))))

  (def cadar (lambda (cons)
               (car (cdr (car cons)))))

  (def do (lambda (fn list)
            (if (nil? list)
                nil
                ((lambda ()
                   (fn (car list))
                   (do fn (cdr list)))))))
  
  (def map (lambda (fn list)
             (if (nil? list)
                 nil
                 (cons (fn (car list))
                       (map fn (cdr list))))))

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

  (def last (lambda (list)
              (if (nil? list)
                  nil
                  (if (nil? (cdr list))
                      (car list)
                      (last (cdr list))))))

  (def nth-cdr (lambda (list n)
                 (if (= n 0)
                     list
                     (nth-cdr (cdr list) (- n 1)))))

  (def length (lambda (list)
                ((lambda (loop)
                   (loop list 0 loop))
                 (lambda (list counter loop)
                   (if (nil? list)
                       counter
                       (loop (cdr list) (+ counter 1) loop))))))

  (def append (lambda (&rest lists)
                (if (= (length lists) 0)
                    nil
                    (if (= (length lists) 1)
                        (car lists)
                        (if (nil? (cdr (car lists)))
                            (cons (car (car lists))
                                  (apply append (cdr lists)))
                            (cons (car (car lists))
                                  (apply append (cons (cdr (car lists)) (cdr lists))))))))))

(defmacro progn (&rest body)
  (list (cons 'lambda (cons '() body))))

(defmacro let (bindings &rest body)
  (cons (cons 'lambda (cons (map car bindings) body))
        (map cadr bindings)))

(defmacro let* (bindings &rest body)
  (if (nil? bindings)
      (list (cons 'lambda (cons '() body)))
      (cons (list 'lambda (list (caar bindings))
                  (apply let* (cons (cdr bindings) body)))
            (cdar bindings))))

(defmacro cond (&rest clauses)
  (if (nil? clauses)
      nil
      (list 'if (caar clauses) (cadar clauses)
            (cons 'cond (cdr clauses)))))

(defmacro and (&rest exprs)
  (cond ((nil? exprs) t)
        ((nil? (cdr exprs)) (car exprs))
        (t (list 'if (car exprs)
                 (cons 'and (cdr exprs))
                 nil))))

(defmacro or (&rest exprs)
  (cond ((nil? exprs) nil)
        ((nil? (cdr exprs)) (car exprs))
        (t (list 'if (car exprs)
                 t
                 (cons 'or (cdr exprs))))))


(defmacro quasiquote (exprs)
  (cons 'append (map (lambda (expr)
                       (cond ((and (cons? expr) (= (car expr) 'unquote))
                              (list 'list (cadr expr)))
                             ((and (cons? expr) (= (car expr) 'unquote-splice))
                              (cadr expr))
                             ((cons? expr)
                              (list 'list (quasiquote expr)))
                             (t
                              (list 'list (list 'quote expr)))))
                     exprs)))


(def fold (lambda (fn list)
            (let ((acc (car list)))
              (do (lambda (e)
                    (set! acc (fn acc e)))
                  (cdr list))
              acc)))

(def find (lambda (list pred)
            (let ((loop (lambda (list pred counter loop)
                          (if (nil? list)
                              nil
                              (if (pred (car list))
                                  counter
                                  (loop (cdr list) pred (+ counter 1) loop))))))
              (loop list pred 0 loop))))

(def insert! (lambda (list e n)
               (let ((loop (lambda (list c loop)
                             (if (nil? list)
                                 nil
                                 (if (= c n)
                                     (setcdr list (cons e (cdr list)))
                                     (loop (cdr list) (+ c 1) loop))))))
                 (loop list 1 loop))))
