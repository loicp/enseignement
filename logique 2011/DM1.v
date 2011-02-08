(*
montrer en Coq que le club �cossais n'a pas de membre,
 uniquement avec les tactiques du TD:
– Tout membre non écossais porte des chaussettes rouges.
– Tout membre porte un kilt ou ne porte pas de chaussettes rouges.
– Les membres mariés ne sortent pas le dimanche.
– Un membre sort le dimanche si et seulement s’il est écossais.
– Tout membre qui porte un kilt est écossais et marié.
– Tout membre écossais porte un kilt.
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