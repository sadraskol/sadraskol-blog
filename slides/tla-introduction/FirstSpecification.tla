-------------------------- MODULE FirstSpecification --------------------------
EXTENDS Naturals

VARIABLE reservations

Coaches == { "A", "B" }
SeatNumbers == 1..10
Seats == Coaches \X SeatNumbers

----

Reserve == reservations' = reservations \union {{<<"A", 1>>}}

----

Init == reservations = {}
Next == Reserve

=============================================================================