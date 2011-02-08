(*
montrer en Coq que le club écossais n'a pas de membre,
 uniquement avec les tactiques du TD:
*)

Variables A B C D E:Prop.
Definition f1 := not A -> B.
Definition f2 := C \/ not B.
Definition f3 := D -> not E.
Definition f4 := (E -> A) /\ (A -> E).
Definition f5 := C -> A /\ D.
Definition f6 := A -> C.

Lemma club_ecossais : not (f1 /\ f2 /\ f3 /\ f4 /\ f5 /\ f6).
unfold f1, f2,f3,f4,f5,f6.
...
Qed.