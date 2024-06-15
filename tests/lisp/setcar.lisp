(let ((list (list 1 2 3 4)))
  (setcar list 5)
  (print list)
  (assert (= list (list 5 2 3 4))))
