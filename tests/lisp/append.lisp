(assert (= (append (list 1 2 3 4) (list 5 6 7 8))
           (list 1 2 3 4 5 6 7 8)))

(assert (= (append (list nil) (list 1))
           (list nil 1)))

