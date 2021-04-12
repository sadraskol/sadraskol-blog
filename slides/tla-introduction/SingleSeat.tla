----------------------------- MODULE SingleSeat -----------------------------
EXTENDS Naturals

VARIABLE reservations

Coaches == { "A", "B" }
SeatNumbers == 1..10
Seats == Coaches \X SeatNumbers

----

Reserve == \E seat \in Seats : reservations' = reservations \union {{seat}}

----

Init == reservations = {}
Next == Reserve

=============================================================================