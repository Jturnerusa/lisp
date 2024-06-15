(let ((list (list "1" "2" "3" "5")))
  (insert list "4" 3)
  (assert (= list (list "1" "2" "3" "4" "5"))))
