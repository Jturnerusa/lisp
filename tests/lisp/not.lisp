(def not_eq (lambda (a b)
              (not (= a b))))

(assert (not false))
(assert (not (not true)))
(assert (not (not_eq 1 1)))
