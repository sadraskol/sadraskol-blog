---------------------- MODULE OverlappingReservations ----------------------
EXTENDS Naturals, FiniteSets

VARIABLE reservations

Coaches == { "A", "B" }
SeatNumbers == 1..10
Seats == Coaches \X SeatNumbers

----

70PercentTrainOccupation == (70 * Cardinality(Seats)) \div 100

ReservedSeats == UNION reservations

Reserve(count) ==
    /\ Cardinality(ReservedSeats) + count <= 70PercentTrainOccupation
    /\ \E seats \in SUBSET Seats:
        /\ Cardinality(seats) = count
        /\ reservations' = reservations \union {seats}

----

Init == reservations = {}
Next == \E seatCount \in 1..Cardinality(Seats): Reserve(seatCount)

----

AtMost70PercentTrainOccupation == Cardinality(UNION reservations) <= 70PercentTrainOccupation

SeatsReservedOnce ==
    \A seat \in Seats:
    \A r1 \in reservations:
    \A r2 \in reservations:
        (seat \in r1 /\ seat \in r2) => (r1 = r2)

=============================================================================
