  ;; Some primitive operations like car, cdr, cons, etc are implemented
  ;; as special operations in the compiler and aren't bound to a symbol
  ;; as functions. This makes (map car (list (cons 'a 'b))) for example
  ;; not work, so we create some functions with the same name as builtins
  ;; that just call the builtin internally.

  ;; These functions also should be available at compile time so they can
  ;; be used in macros.

(eval-when-compile

  (def (car (fn (list 't) -> 't))
      (lambda (list)
        (car list)))

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

    (def (map (fn (fn 't -> 'u) (list 't) -> (list 'u)))
        (lambda (fn list)
          (if (nil? list)
              nil
              (cons (fn (car list))
                    (map fn (cdr list)))))))

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
