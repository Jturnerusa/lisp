(def fac (lambda (f)
            (if (< f 2)
                f
                (* f (fac (- f 1))))))

(print (fac 10))
