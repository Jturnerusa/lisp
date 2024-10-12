(defun (make-vec-with-capacity int 'a -> (vec 'a)) (capacity init)
  (let ((vec (make-vec)))
    (let loop ((counter 0))
         (if (>= counter capacity)
             vec
             (progn
               (vec-push! vec init)
               (loop (+ counter 1)))))))

(defun (vec-map (fn 'a -> 'b) (vec 'a) -> (vec 'b)) (fn a)
  (let ((b (make-vec)))
    (let loop ((counter 0))
         (if (>= counter (vec-length a))
             b
             (progn
               (vec-push! b (fn (vec-index a counter)))
               (loop (+ counter 1)))))))

(defun (vec->list (vec 'a) -> (list 'a)) (vec)
  (let loop ((counter 0))
       (if (>= counter (vec-length vec))
           nil
           (cons (vec-index vec counter) (loop (+ counter 1))))))

(defun (list->vec (list 'a) -> (vec 'a)) (list)
  (let ((vec (make-vec)))
    (let loop ((list list))
         (if (nil? list)
             vec
             (progn
               (vec-push! vec (car list))
               (loop (cdr list)))))))
