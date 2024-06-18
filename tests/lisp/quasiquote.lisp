(defmacro test-unquote (a)
  `(+ ,a 1))

(defmacro test-splice (a)
  `(+ ,@a))

(assert (= (test-unquote 1) 2))

(assert (= (test-splice (1 1)) 2))
