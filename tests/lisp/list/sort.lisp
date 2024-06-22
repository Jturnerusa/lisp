(assert (= (sort '(5 9 8 6 7 3 4 2 1) (lambda (a b)
                                        (< a b)))
           '(1 2 3 4 5 6 7 8 9)))
