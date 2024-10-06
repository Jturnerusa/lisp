  ;; Some primitive operations like car, cdr, cons, etc are implemented
  ;; as special operations in the compiler and aren't bound to a symbol
  ;; as functions. This makes (map car (list (cons 'a 'b))) for example
  ;; not work, so we create some functions with the same name as builtins
  ;; that just call the builtin internally.

  ;; These functions also should be available at compile time so they can
  ;; be used in macros.

(deftype result
  (ok 'a)
  (err 'b))

(deftype hlist
    (hlist (list hlist))
    (symbol symbol)
    (string string)
    (char char)
    (int int)
    (bool bool)
    (nil))             

(eval-when-compile

  (deftype option (some 't) (none))

  (def (car (fn (list 't) -> 't))
      (lambda (list)
        (car list)))

  (def (cdr (fn (list 't) -> (list 't)))
      (lambda (list)
        (cdr list)))

  (def (+ (fn int int -> int))
      (lambda (a b)
        (+ a b)))

  (def (not (fn bool -> bool))
      (lambda (t)
        (= t false)))

  (def (cadr (fn (list 't) -> 't))
      (lambda (list)
        (car (cdr list))))
  
    (def (caar (fn (list (list 't)) -> 't))
        (lambda (list)
          (car (car list))))

    (def (do (fn (fn 't -> nil) (list 't) -> nil))
        (lambda (fn list)
          (if (nil? list)
              nil
              ((lambda ()
                 (fn (car list))
                 (do fn (cdr list)))))))

    (def (cdar (fn (list (list 't)) -> (list 't)))
        (lambda (list)
          (cdr (car list))))

    (def (cadar (fn (list (list 't)) -> 't))
        (lambda (list)
          (car (cdr (car list)))))

    (def (map (fn (fn 't -> 'u) (list 't) -> (list 'u)))
        (lambda (fn list)
          (if (nil? list)
              nil
              (cons (fn (car list))
                    (map fn (cdr list))))))

    (def (filter (fn (fn 't -> bool)
                     (list 't)
                     -> (list 't)))
        (lambda (pred list)
          (if (nil? list)
              nil
              (if (pred (car list))
                  (cons (car list) (filter pred (cdr list)))
                  (filter pred (cdr list))))))

    (def (length (fn (list 't) -> int))
        (lambda (list)
          (letrec ((loop (lambda (list counter)
                           (if (nil? list)
                               counter
                               (loop (cdr list) (+ counter 1))))))
            (loop list 0))))
          

    (def (append (fn &rest (list 't) -> (list 't)))
        (lambda (&rest lists)
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

(defmacro let* (bindings &rest body)
  (if (nil? bindings)
      (list (cons 'lambda (cons '() body)))
      (cons (list 'lambda (list (caar bindings))
                  (cons 'let* (cons (cdr bindings) body)))
            (cdar bindings))))

(defmacro cond (&rest clauses)
  (if (nil? clauses)
      nil
      (if (= (caar clauses) 'true)
          (cadar clauses)
          (list 'if (caar clauses)
                (cadar clauses)
                (cons 'cond (cdr clauses))))))

(defmacro and (&rest exprs)
  (cond ((nil? exprs) false)
        ((nil? (cdr exprs)) (list 'if (car exprs) 'true 'false))
        (true (list 'if (car exprs)
                 (cons 'and (cdr exprs))
                 false))))

(defmacro or (&rest exprs)
  (cond ((nil? exprs) false)
        ((nil? (cdr exprs)) (car exprs))
        (true (list 'if (car exprs)
                    true
                    (cons 'or (cdr exprs))))))

(defmacro quasiquote (exprs)
  (cons 'append (map (lambda (expr)
                       (cond ((and (cons? expr) (= (car expr) 'unquote))
                              (list 'list (cadr expr)))
                             ((and (cons? expr) (= (car expr) 'unquote-splice))
                              (cadr expr))
                             ((cons? expr)
                              (list 'list (list 'quasiquote expr)))
                             (true
                              (list 'list (list 'quote expr)))))
                     exprs)))

(defmacro let (bindings &rest body)
  (if (symbol? bindings)
      `(letrec ((,bindings (lambda ,(map car (car body))
                             ,@(cdr body))))
         (,bindings ,@(map cadr (car body))))
      `((lambda ,(map car bindings)
          ,@body)
        ,@(map cadr bindings))))

(defmacro when (pred body)
  `(if ,pred ,body nil))

(defmacro unless (pred body)
  `(if ,pred nil ,body))

(defmacro named-let (name bindings &rest body)
  `(letrec ((,name (lambda ,(map car bindings)
                    ,@body)))
     (,name ,@(map cadr bindings))))

(defmacro typecase (x &rest arms)
  (if (= 0 (length arms))
      nil
      (if (= 'else (caar arms))
          (cadar arms)
          `(if-let ,x ,(caar arms)
             ,(cadar arms)
             (typecase ,x ,@(cdr arms))))))

(defmacro defun (def parameters &rest body)
  `(def ,(if (cons? def)
             `(,(car def) ,(cons 'fn (cdr def)))
             def)
       (lambda ,parameters
         ,@body)))

(eval-when-compile
  (defun (panic 'a -> any) (message)
    (print message)
    (assert false))

  (defun (fold (fn 'a 'a -> 'a) (list 'a) -> 'a) (fn list)
    (letrec ((loop (lambda (acc list)
                     (if (nil? list)
                         acc
                         (loop (fn acc (car list)) (cdr list))))))
      (loop (car list) (cdr list))))

  (defun (nth (list 'a) int -> (option 'a)) (list n)
    (named-let loop ((counter 0)
                     (list list))
      (if (nil? list)
          (option-none)
          (if (> counter (- n 1))
              (option-some (car list))
              (loop (+ counter 1) (cdr list))))))

  (defun (any? (fn 'a -> bool) (list 'a) -> bool) (fn list)
    (if (nil? list)
        false
        (if (fn (car list))
            true
            (any? fn (cdr list)))))

  (defun (option-map (fn 'a -> 'b) (option 'a) -> (option 'b)) (fn option)
    (typecase option
      ((option-some some)
       (option-some (fn some)))
      (else
       (option-none))))

  (defun (option-and-then (fn 'a -> (option 'b))
                          (option 'a)
                          -> (option 'b))
      (fn option)
    (typecase option
      ((option-some some)
       (fn some))
      (else
       (option-none))))

  (defun (option-unwrap (option 'a) -> 'a) (option)
    (typecase option
      ((option-some some)
       some)
      (else
       (panic))))

  (defun (option-some? (option 'a) -> bool) (option)
    (typecase option
      ((option-some _)
       true)
      (else
       false)))

  (defun (option-none? (option 'a) -> bool) (option)
    (not (option-some? option)))

  (defun (option-collect (list (option 'a)) -> (option (list 'a))) (options)
    (if (any? option-none? options)
        (option-none)
        (option-some (map option-unwrap options))))

  (defun (filter-map (fn 'a -> (option 'b))
                     (list (option 'a))
                     -> (list 'b))
      (fn list)
    (let loop ((list list))
         (if (nil? list)
             nil
             (let ((element (car list)))
               (if-let (fn element) (option-some a)
                 (cons a (loop (cdr list)))
                 (loop (cdr list))))))))
