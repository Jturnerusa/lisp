(let ((list (list 1 2 3 4)))
  (setcdr (cdr list) nil)
  (assert (= list (list 1 2))))
