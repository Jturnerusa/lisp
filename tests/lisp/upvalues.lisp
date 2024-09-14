(def (upvalues (fn int -> int))
    (lambda (test)
      ((lambda ()
         ((lambda ()
            test))))))

(= (upvalues 1) 1)
