(def hm (map-create))

(map-insert! hm "hello" 'world)

(print hm)

(assert (= (map-retrieve hm "hello") 'world))
