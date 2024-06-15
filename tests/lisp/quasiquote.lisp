(defmacro ++ (a)
  `(+ ,a 1))

(assert (= (++ 1) 2))
