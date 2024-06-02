(def upvalues (lambda (test)
                ((lambda ()
                   ((lambda ()
                      test))))))

(= (upvalues 1) 1)
