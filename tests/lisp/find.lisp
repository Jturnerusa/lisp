(let* ((list (list "1" "2" "3" "4"))
       (position (find list (lambda (e) (= e "4")))))
  (assert (= position 3)))
