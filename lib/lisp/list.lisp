(module list)

(def take (lambda (list n)
            (cond ((nil? list)
                   nil)
                  ((= n 0)
                   nil)
                  (true
                   (cons (car list) (take (cdr list) (- n 1)))))))

(def drop (lambda (list n)
            (cond ((nil? list)
                   nil)
                  ((= n 1)
                   (cdr list))
                  (true
                   (drop (cdr list) (- n 1))))))

(def merge (lambda (l r pred)
             (cond ((nil? l)
                    r)
                   ((nil? r)
                    l)
                   ((pred (car l) (car r))
                    (cons (car l) (merge (cdr l) r pred)))
                   (true
                    (cons (car r) (merge l (cdr r) pred))))))

(def sort (lambda (list pred)
            (cond ((nil? list)
                   nil)
                  ((< (length list) 2)
                   list)
                  (true
                   (let* ((mid (/ (length list) 2))
                          (l (take list mid))
                          (r (drop list mid)))
                     (merge (sort l pred) (sort r pred) pred))))))

(export take)
(export drop)
(export sort)
