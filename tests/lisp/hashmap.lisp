(def hm (map-create))

(map-insert! hm "hello" 'world)

(assert (= (map-retrieve hm "hello") 'world))
