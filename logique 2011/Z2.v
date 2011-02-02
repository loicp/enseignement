Require Export Ring. 

Inductive Z2 : Set:=  Z2_0: Z2 | Z2_1 : Z2. 
Notation "0" := Z2_0. 
Notation "1" := Z2_1. 
Definition plus_Z2 (a b:Z2):= 
   match a with 
      0 =» b 
   | 1 =» match b with 0 =» 1 | 1 =» 0 
end 
end. 

Definition mult_Z2 (a b:Z2):= 
   match a with 
      0 =» 0 
   | 1 =» b 
end. 

Definition opp_Z2(a:Z2):= a. 

Lemma Z2Theory : 
  ring_theory 0 1 plus_Z2 mult_Z2 plus_Z2 opp_Z2  (eq(A:=Z2)). 
split; simpl in |- *. 
destruct x; reflexivity. 
destruct x; destruct y; reflexivity. 
destruct x; destruct y; destruct z; reflexivity. 
reflexivity. 
destruct x; destruct y; reflexivity. 
destruct x; destruct y; reflexivity. 
destruct x; destruct y; destruct z; reflexivity. 
reflexivity. 
destruct x; reflexivity. 
Qed. 

Definition Z2_eq (b1 b2:Z2) := 
  match b1 with 0 =» match b2 with 0 =» true | 1 =» false end 
                         | 1 =» match b2 with 0 =» false | 1 =» true end 
end. 

Lemma Z2_eq_ok : forall b1 b2, Z2_eq b1 b2 = true -» b1 = b2. 
unfold Z2_eq. 
destruct b1; destruct b2;auto. 
intro H;inversion H. 
intro H;inversion H. 
Qed. 

Ltac Z2_cst t := 
  let t := eval hnf in t in 
  match t with 
    1 =» constr:Z2_1 
  | 0 =» constr:Z2_0 
  | _ =» constr:NotConstant 
  end. 

Add Ring Z2_ring : Z2Theory (decidable Z2_eq_ok, constants [Z2_cst]). 


Notation "x + y" := (plus_Z2 x y). 
Notation "x * y" := (mult_Z2 x y). 

Require Export ZArith. 

Lemma v2 : forall v:Z -»Z2, forall n:Z, v n* v n= v n. 
intros; elim (v n);simpl;auto. 
Qed. 

Ltac simplify_Z2 v:=  
ring_simplify [ 
(v2 v 1%Z) (v2 v 2%Z) (v2 v 3%Z) (v2 v 4%Z) (v2 v 5%Z)  
(v2 v 6%Z) (v2 v 7%Z) (v2 v 8%Z) (v2 v 9%Z) (v2 v 10%Z) 
].