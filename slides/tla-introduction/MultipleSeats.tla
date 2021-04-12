--------------------------- MODULE MultipleSeats ---------------------------
EXTENDS Naturals, FiniteSets

VARIABLE reservations

Coaches == { "A", "B" }
SeatNumbers == 1..10
Seats == Coaches \X SeatNumbers

----

70PercentTrainOccupation == (70 * Cardinality(Seats)) \div 100

ReservedSeats == UNION reservations

Reserve(count) ==
    /\ Cardinality(ReservedSeats) < 70PercentTrainOccupation
    /\ \E seats \in SUBSET Seats:
        /\ Cardinality(seats) = count
        /\ reservations' = reservations \union {seats}

----

Init == reservations = {}
Next == \E seatCount \in 1..Cardinality(Seats): Reserve(seatCount)

----

AtMost70PercentTrainOccupation == Cardinality(UNION reservations) <= 70PercentTrainOccupation

=============================================================================
