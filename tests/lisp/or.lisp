(assert (= (or t nil) t))
(assert (= (or t t) t))
(assert (= (or nil t) t))
(assert (= (or nil nil) nil))
