---------------------- MODULE TrainOccupationInvariant ----------------------
EXTENDS Naturals, FiniteSets

VARIABLE reservations

Coaches == { "A", "B" }
SeatNumbers == 1..10
Seats == Coaches \X SeatNumbers

----

70PercentTrainOccupation == (70 * Cardinality(Seats)) \div 100

Reserve == \E seat \in Seats : reservations' = reservations \union {{seat}}

----

Init == reservations = {}
Next == Reserve

----

AtMost70PercentTrainOccupation == Cardinality(UNION reservations) <= 70PercentTrainOccupation

=============================================================================
