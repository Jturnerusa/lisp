(def square (lambda (x)
              (* x 2)))

(def expected 4)

(if (= (square 2) expected)
    t
    (panic "failure"))
