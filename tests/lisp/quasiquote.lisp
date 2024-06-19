(let ((a 1))
  (assert (= `(,a (,a) ,@(list a 'a) a)
             '(1 (1) 1 a a))))
