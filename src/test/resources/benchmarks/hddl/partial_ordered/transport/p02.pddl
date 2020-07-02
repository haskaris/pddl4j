(define (problem p02)
 (:domain transport)
 (:objects
  city-loc-0 city-loc-1 city-loc-2 city-loc-3 - location
  truck-0 - vehicle
  package-0 package-1 package-2 - package
  capacity-0 capacity-1 capacity-2 - capacity-number
 )
 (:htn
  :subtasks (and
   (deliver package-0 city-loc-1)
   (deliver package-1 city-loc-0)
   (deliver package-2 city-loc-0)
   )
  :ordering ( )
  :constraints ( ))
 (:init
  (capacity-predecessor capacity-0 capacity-1)
  (capacity-predecessor capacity-1 capacity-2)
  (road city-loc-0 city-loc-3)
  (road city-loc-1 city-loc-2)
  (road city-loc-1 city-loc-3)
  (road city-loc-2 city-loc-1)
  (road city-loc-3 city-loc-0)
  (road city-loc-3 city-loc-1)
  (at package-0 city-loc-3)
  (at package-1 city-loc-2)
  (at package-2 city-loc-2)
  (at truck-0 city-loc-3)
  (capacity truck-0 capacity-2)
 )
)