(def (take function)
     (lambda ((list (union (list (generic t)) nil))
              (n int)) -> (union (list (generic t)) nil)
            (cond ((= n 0)
                   nil)
                  ((cons? list)
                   (cons (car list) (take (cdr list) (- n 1)))))))

(def (drop function)
     (lambda ((list (generic t))
              (n int)) -> (list (generic t))
            (cond ((nil? list)
                   nil)
                  ((= n 1)
                   (cdr list))
                  (true
                   (drop (cdr list) (- n 1))))))

(def (merge function)
     (lambda ((l (list (generic t)))
              (r (list (generic t)))
              (pred (function (generic t) (generic t) -> bool)))
             (cond ((nil? l)
                    r)
                   ((nil? r)
                    l)
                   ((pred (car l) (car r))
                    (cons (car l) (merge (cdr l) r pred)))
                   (true
                    (cons (car r) (merge l (cdr r) pred))))))

(def (sort function)
     (lambda ((list (list (generic t)))
              (pred (function (generic a) (generic b) -> (list generic)))) -> (list (generic t))
       (cond ((nil? list)
              nil)
             ((< (length list) 2)
              list)
             (true
              (let* ((mid (/ (length list) 2))
                     (l (take list mid))
                     (r (drop list mid)))
                (merge (sort l pred) (sort r pred) pred))))))
