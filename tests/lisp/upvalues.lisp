(def upvalues (lambda (test)
                ((lambda ()
                   ((lambda ()
                      (print test)))))))

(upvalues 1)
