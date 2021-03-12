(define (problem mysty-x-9)
   (:domain mystery-typed)
   (:objects apple flounder haroset hamburger wurst hotdog guava
             - food
             entertainment intoxication curiosity excitement - pleasure
             dread sciatica abrasion prostatitis loneliness anger
             hangover anxiety laceration boils jealousy angina grief - pain
             bosnia bavaria arizona manitoba kentucky - province
             earth uranus saturn venus - planet)
   (:init (eats apple guava)
          (eats guava apple)
          (locale hotdog bavaria)
          (locale wurst bavaria)
          (craves hangover haroset)
          (craves loneliness haroset)
          (eats hamburger haroset)
          (harmony intoxication uranus)
          (craves laceration wurst)
          (craves anxiety wurst)
          (eats flounder hamburger)
          (locale hamburger bosnia)
          (harmony excitement uranus)
          (craves anger haroset)
          (craves curiosity hotdog)
          (craves dread flounder)
          (attacks bavaria arizona)
          (harmony entertainment venus)
          (craves intoxication haroset)
          (eats hamburger flounder)
          (craves angina guava)
          (eats haroset guava)
          (attacks bosnia bavaria)
          (eats hotdog wurst)
          (eats guava haroset)
          (eats hotdog apple)
          (craves excitement guava)
          (craves jealousy guava)
          (craves sciatica flounder)
          (craves grief guava)
          (eats flounder wurst)
          (craves boils guava)
          (eats apple hotdog)
          (eats wurst flounder)
          (craves entertainment flounder)
          (attacks arizona manitoba)
          (orbits earth uranus)
          (locale haroset arizona)
          (eats wurst hotdog)
          (harmony curiosity uranus)
          (orbits uranus saturn)
          (craves prostatitis haroset)
          (orbits saturn venus)
          (craves abrasion haroset)
          (locale flounder arizona)
          (locale guava kentucky)
          (attacks manitoba kentucky)
          (locale apple arizona)
          (eats haroset hamburger))
   (:goal (and (craves sciatica hamburger)
               (craves jealousy wurst))))