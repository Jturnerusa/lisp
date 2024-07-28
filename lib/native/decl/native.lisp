(decl print (lambda (string)))

(decl argv (lambda ()))

(decl read-file (lambda (string)))

(decl is-digit? (lambda ((s string)) -> bool))

(decl string-split-whitespace (lambda (string)))

(decl string->int (lambda (string)))

(decl string-contains? (lambda ((haystack string)
                                (needle (union string char)))
                         -> string))

(decl string-substr (lambda ((s string)
                             (start int)
                             (stop int))
                      -> string))

(decl string-find (lambda ((haystack string)
                           (needle string))
                    -> (union int nil)))

(decl string->list (lambda ((s string)) -> (list char)))
