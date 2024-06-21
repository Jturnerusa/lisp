(def named-let-test (lambda (n)
                      (named-let loop ((counter n))
                        (if (> counter 0)
                            (loop (- counter 1))
                            counter))))

(assert (= (named-let-test 10) 0))
