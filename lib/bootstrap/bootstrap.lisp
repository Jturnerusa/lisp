  ;; Some primitive operations like car, cdr, cons, etc are implemented
  ;; as special operations in the compiler and aren't bound to a symbol
  ;; as functions. This makes (map car (list (cons 'a 'b))) for example
  ;; not work, so we create some functions with the same name as builtins
  ;; that just call the builtin internally.

  ;; These functions also should be available at compile time so they can
  ;; be used in macros.

(eval-when-compile

  (def car (lambda ((cons (list `t))) -> `t
             (car cons)))

  (def + (lambda ((a int) (b int)) -> int
           (+ a b)))

  (def not (lambda ((t bool)) -> bool
             (= t false)))

  (def cadr (lambda ((cons (list `t))) -> `t
              (car (cdr cons))))

  (def caar (lambda ((cons (list (list `t)))) -> `t
              (car (car cons))))

  (def cddr (lambda ((cons (list `t))) -> (list `t)
              (cdr (cdr cons))))

  (def cdar (lambda ((cons (list (list `t)))) -> (list `t)
              (cdr (car cons))))

  (def cadar (lambda ((cons (list (list `t)))) -> `t
               (car (cdr (car cons)))))

  (def do (lambda ((fn (fn `t -> `u))
                   (list (list `t)))
                  -> nil
            (if (nil? list)
                nil
                ((lambda () -> nil
                         (fn (car list))
                         (do fn (cdr list)))))))
  
  (def map (lambda ((fn (fn `t -> `u))
                    (list (list `t)))
                   -> (list `u)
             (if (nil? list)
                 nil
                 (cons (fn (car list))
                       (map fn (cdr list))))))

  (def filter (lambda ((pred (fn `t -> bool))
                       (list (list `t)))
                      -> (list `t)
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

;; This impl is a temporary solution.
;; This can be more cleanly implemented using the Z combinator, but
;; this lisps type system is not yet capable of expressing Z.
(defmacro named-let (name bindings &rest body)
  (let ((tmp (gensym)))
    `(let* ((,name nil)
            (,tmp (lambda ,(map car bindings)
                     ,@body)))
       (set! ,name ,tmp)
       (assert (function? ,name))
       (,name ,@(map cadr bindings)))))

(defmacro if-let* (bindings then else)
  `(let ((,(caar bindings) ,(car (cdr (car bindings)))))
     ,(named-let loop ((bindings bindings))
        (if (= (length bindings) 1)
            `(if (nil? ,(caar bindings)) then else)
            `(let ((,(car (car (cdr bindings))) (if (nil? ,(caar bindings))
                                                    nil
                                                    ,(car (cdar (cdr bindings))))))
               ,(loop (cdr bindings)))))))

(defmacro when-let* (bindings &rest body)
  `(let ((,(caar bindings) ,(car (cdr (car bindings)))))
     ,(named-let loop ((bindings bindings))
        (if (= (length bindings) 1)
            `(if (nil? ,(caar bindings)) nil (progn ,@body))
            `(let ((,(car (car (cdr bindings))) (if (nil? ,(caar bindings))
                                                    nil
                                                    ,(car (cdar (cdr bindings))))))
               ,(loop (cdr bindings)))))))

(defmacro when (pred body)
  `(if ,pred ,body nil))

(defmacro unless (pred body)
  `(if ,pred nil ,body))

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
