(def fac (lambda (n)
           (if (< n 2)
               n
               (* n (fac (- n 1))))))

(print (fac 10))
