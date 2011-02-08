(* Preuves en calcul des propositions avec Coq *)
 
(* A:Prop signifie que A est de type Prop, i.e. A est une proposition.
Dans Coq, chaque objet a un type.
Syntaxe  propre à Coq:
forall désigne le quantificateur "quelque soit" e mathématiques,
et la flèche -> désigne l'implication "=>"
ne pas oublier la virgule *)
 
(* première démonstration: pour démontrer un lemme, on tape la commande "Lemma",
puis on donne un nom au lemme, suivi de ":" et par son énoncé,
et toujours un point à la fin. *)
 
Lemma l1: forall A:Prop, A -> A.
 
(* première tactique de preuve:
en math on dirait: soit A une proposition, montrons A -> A
en Coq on dit: *) 
intro A.
(* pour démontrer A -> A, supposons que A est vrai, appelons cette hypothèse "H",
et démontrons A: *)
intro H.
(* on doit démontrer A, mais on l'a en hypothèse: c'est H *)
exact H.
(* la preuve est finie: sauvegardons-la *)
Qed.
 
(* Vérifions que maintenant le système Coq connais notre lemme: *)
Check l1.
 
(* on connait maintenant 2 tactiques:
intro nom.
exact nom.
*)
 
(* preuves de tautologies plus compliquées: conjonctions, disjonctions, négations *)
 
Lemma l2: forall A B:Prop, A /\ B -> A.
(* variante de "intro": introduction de plusieurs variables ou hypothèses: *)
intros A B H.
(* H est une conjonction de 2 propositions, 
qu'on souhaiterait poser en hypothèses séparées : *)
destruct H as [H1 H2].
exact H1.
Qed.
 
(* on connait maintenant 4 tactiques:
intro nom.
intros nom1 nom2 ... .
exact nom.
destruct nom as [nom1 nom2 ...].
*)
 
Lemma l3: forall A B:Prop, A -> A \/ B.
intros A B H.
(* il faut choisir: c'est A ou c'est B qui est vrai?
comme on a A en hypothèse, c'est A, i.e. le terme de gauche de la disjonction,
et gauche se dit "left" en anglais: *)
left.
exact H.
Qed.
 
Lemma l4: forall A B:Prop, (A -> A \/ B) /\ (B -> A \/ B).
intros A B.
(* il faut démontrer deux choses, en fait: 
A -> A \/ B
et
B -> A \/ B
séparons-les (split = séparer en anglais): *)
split.
(* là, on voit apparaître deux preuves à faire, deux "buts" de Coq à démontrer;
les tactiques concernent uniquement le premier but, quand il sera démontré, il disparaîtra
et le second prendra sa place... *)
intro H. left. exact H.
(* voilà, le deuxième but est là *)
intro H.
(* logique, si on connait "droit" en anglais: *)
right.
exact H.
Qed.
 
(* on connait maintenant 6 tactiques:
intro nom.
intros nom1 nom2 ... .
exact nom.
destruct nom as [nom1 nom2 ...].
left.
right.
split.
*)
 
Lemma l5: forall A B:Prop, A \/ B -> B \/ A.
intros A B H.
(* là, on ne peut pas choisir qui de A ou B est vrai: cela dépend de H!
il faut traiter les deux cas possible pour H: *)
destruct H.
(* on ne le voit pas, mais le deuxième but contient une hypothèse que B est vraie.
maintenant on peut choisir: *)
right. exact H.
(* le deuxième cas apparaît: c'est B qui est supposé vrai *)
left. exact H.
Qed.
 
(* on connait maintenant 7 tactiques:
intro nom.
intros nom1 nom2 ... .
exact nom.
destruct nom as [nom1 nom2 ...].
destruct nom.
left.
right.
split.
*)
 
Lemma l6: forall A B:Prop,  A /\ (A -> B) -> B.
intros A B H. destruct H as [H1 H2].
(* H2 permet de démontrer B, si on sait que A est vraie: appliquons là a notre but
qui est justement B: *)
apply H2.
(* il faut maintenant démontrer A, qui était l'hypothèse de H2. *)
exact H1.
Qed.
 
(* on connait maintenant 7 tactiques avec leurs variantes:
intro: intro nom.
      intros nom1 nom2 ... .
exact nom.
destruct: destruct nom as [nom1 nom2 ...].
         destruct nom.
left.
right.
split.
apply nom.
*)
(*
à vous:
 
Lemma l7: forall A B C D:Prop,
A -> (A -> B) -> (B -> C) -> (C -> D) -> D.
 
Lemma l8: forall A B C:Prop,
  (A /\ (B \/ C) -> A /\ B \/ A /\ C).
/\ (A /\ B \/ A /\ C -> A /\ (B \/ C)).
 
Lemma l9: forall A B C:Prop,
  (A \/ B /\ C -> (A \/ B) /\ (A \/ C)).
/\ ((A \/ B) /\ (A \/ C) -> A \/ B /\ C).
*)
 
Lemma l10: forall A:Prop, A -> not (not A).
(* Coq affiche ~A pour "not A"
en fait, dans Coq, not A est une abréviation de A -> False, 
où False est une proposition sans preuve. 
Remplaçons not A par sa définition: *)
unfold not.
intros A H1 H2. apply H2. exact H1. Qed.
 
Lemma l11: forall A B:Prop, A \/ B -> not (not A /\ not B).
 
Lemma l12: forall A B:Prop, not (A \/ B) -> not A /\ not B.
 
Lemma Jack_Palmer : forall A B C D:Prop,
(not A -> B \/ C) /\ ( not B -> not A /\ D) /\ (D -> B \/ not C) -> not (not B).