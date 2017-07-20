From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
Require Import pred prelude ordtype domain unionmap pcm heap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*************************************)
(* Small Partial Commutative Monoids *)
(* can be stored into heaps without  *)
(* universe inconsistencies          *)
(*************************************)

Module SPCM.

Record mixin_of (T : Type) := Mixin {
    valid_op : T -> bool;
    join_op : T -> T -> T;
    unit_op : T;
    _ : commutative join_op;
    _ : associative join_op;
    _ : left_id unit_op join_op;
    (* monotonicity of valid *)
    _ : forall x y, valid_op (join_op x y) -> valid_op x;
    (* unit is valid *)
    _ : valid_op unit_op}.

Section ClassDef.

Notation class_of := mixin_of (only parsing).

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.

Definition pack c := @Pack T c T.
Definition clone := fun c & cT -> T & phant_id (pack c) cT => pack c.

Definition valid := valid_op class.
Definition join := join_op class.
Definition unit := unit_op class.

End ClassDef.

Implicit Arguments unit [cT].

Definition morph_axiom (A B : type) (f : sort A -> sort B) :=
  f unit = unit /\ forall x y, f (join x y) = join (f x) (f y).

Module Exports.
Coercion sort : type >-> Sortclass.
Notation spcm := type.
Notation SPCMMixin := Mixin.
Notation SPCM T m := (@pack T m).

Notation "[ 'spcmMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'spcmMixin'  'of'  T ]") : form_scope.
Notation "[ 'spcm' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'spcm'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'spcm' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'spcm'  'of'  T ]") : form_scope.

Section TOPCM.
Variable U : spcm.
Local Notation tp := (sort U).

Definition pvalid (x : tp) :=  valid x.
Definition pjoin (x1 x2 : tp) := (join x1 x2) : tp.
Definition punit : tp := unit.

Lemma pjoinC (x y : tp) : pjoin x y = pjoin y x.
Proof. by rewrite /pjoin; case: U x y=>T [v j u c *]; apply: c. Qed.

Lemma pjoinA (x y z : tp) : pjoin x (pjoin y z) = pjoin (pjoin x y) z.
Proof. by rewrite /pjoin; case: U x y z=>T [v j y c a *]; apply: a. Qed.

Lemma punitL x : pjoin punit x = x.
Proof. by rewrite /pjoin /punit; case: U x=>T [v j y c a l *]; apply: l. Qed.

Lemma pmonoV x y : pvalid (pjoin x y) -> pvalid x.
Proof.
rewrite /pvalid /pjoin /valid.
by case: U x y=>T [v j y c a l w ????]; apply: w.
Qed.

Lemma pvalidU : pvalid punit.
Proof. by rewrite /pvalid /punit; case: U=>T [v j y c a l w z *]; apply: z. Qed.

Definition spcmPCMMixin := PCMMixin pjoinC pjoinA punitL pmonoV pvalidU.
Canonical spcmPCM := Eval hnf in PCM tp spcmPCMMixin.

End TOPCM.

Coercion spcmPCM : spcm >-> pcm.

End Exports.
End SPCM.

Export SPCM.Exports.

(******************************)
(* Now some PCM constructions *)
(******************************)

(* nats with addition are a pcm *)

Definition natSPCMMixin :=
  SPCMMixin addnC addnA add0n (fun x y => @id true) (erefl _).
Canonical natSPCM := Eval hnf in SPCM nat natSPCMMixin.

(* also with multiplication, but we don't make that one canonical *)

Definition multSPCMMixin :=
  SPCMMixin mulnC mulnA mul1n (fun x y => @id true) (erefl _).
Definition multSPCM := Eval hnf in SPCM nat multSPCMMixin.

(* with max too *)

Definition maxSPCMMixin :=
  SPCMMixin maxnC maxnA max0n (fun x y => @id true) (erefl _).
Definition maxSPCM := Eval hnf in SPCM nat maxSPCMMixin.

Module ProdSPCM.
Section ProdSPCM.
Variables (U V : spcm).
Local Notation tp := (U * V)%type.

Definition pvalid := [fun x : tp => valid x.1 && valid x.2].
Definition pjoin := [fun x1 x2 : tp => (x1.1 \+ x2.1, x1.2 \+ x2.2)].
Definition punit : tp := (Unit, Unit).

Lemma joinC x y : pjoin x y = pjoin y x.
Proof.
move: x y => [x1 x2][y1 y2] /=.
by rewrite (joinC x1) (joinC x2).
Qed.

Lemma joinA x y z : pjoin x (pjoin y z) = pjoin (pjoin x y) z.
Proof.
move: x y z => [x1 x2][y1 y2][z1 z2] /=.
by rewrite (joinA x1) (joinA x2).
Qed.

Lemma validL x y : pvalid (pjoin x y) -> pvalid x.
Proof.
move: x y => [x1 x2][y1 y2] /=.
by case/andP=>D1 D2; rewrite (validL D1) (validL D2).
Qed.

Lemma unitL x : pjoin punit x = x.
Proof. by case: x=>x1 x2; rewrite /= !unitL. Qed.

Lemma validU : pvalid punit.
Proof. by rewrite /pvalid /= !valid_unit. Qed.

End ProdSPCM.
End ProdSPCM.

Definition prodSPCMMixin U V :=
  SPCMMixin (@ProdSPCM.joinC U V) (@ProdSPCM.joinA U V)
            (@ProdSPCM.unitL U V) (@ProdSPCM.validL U V) (@ProdSPCM.validU U V).
Canonical prodSPCM U V := Eval hnf in SPCM (_ * _) (@prodSPCMMixin U V).

(* unit is a pcm; just for kicks *)

Module UnitSPCM.
Section UnitSPCM.

Definition uvalid (x : unit) := true.
Definition ujoin (x y : unit) := tt.
Definition uunit := tt.

Lemma ujoinC x y : ujoin x y = ujoin y x.
Proof. by []. Qed.

Lemma ujoinA x y z : ujoin x (ujoin y z) = ujoin (ujoin x y) z.
Proof. by []. Qed.

Lemma uvalidL x y : uvalid (ujoin x y) -> uvalid x.
Proof. by []. Qed.

Lemma uunitL x : ujoin uunit x = x.
Proof. by case: x. Qed.

Lemma uvalidU : uvalid uunit.
Proof. by []. Qed.

End UnitSPCM.
End UnitSPCM.

Definition unitSPCMMixin :=
  SPCMMixin UnitSPCM.ujoinC UnitSPCM.ujoinA
            UnitSPCM.uunitL UnitSPCM.uvalidL UnitSPCM.uvalidU.
Canonical unitSPCM := Eval hnf in SPCM unit unitSPCMMixin.

(* bools with conjunction are a pcm *)

Module BoolConjSPCM.
Lemma unitL x : true && x = x. Proof. by []. Qed.
End BoolConjSPCM.

Definition boolSPCMMixin := SPCMMixin andbC andbA BoolConjSPCM.unitL
                             (fun x y => @id true) (erefl _).
Canonical boolConjSPCM := Eval hnf in SPCM bool boolSPCMMixin.


(* unionmaps with integer domains are small pcms *)

Section NatMapSPCM.
Variable A : Type.

Let U := union_mapPCM nat_ordType A.

Definition natmapSPCMMixin :=
  SPCMMixin (@joinC U) (@joinA U) (@unitL U) (@validL U) (@valid_unit U).
Canonical natmapSPCM := Eval hnf in SPCM (union_map nat_ordType A) natmapSPCMMixin.

End NatMapSPCM.

(* so are unionmaps with pointer domain *)

Section PtrMapSPCM.
Variable A : Type.
Let U := union_mapPCM ptr_ordType A.

Definition ptrmapSPCMMixin :=
  SPCMMixin (@joinC U) (@joinA U) (@unitL U) (@validL U) (@valid_unit U).
Canonical ptrmapSPCM := Eval hnf in SPCM (union_map ptr_ordType A) ptrmapSPCMMixin.

End PtrMapSPCM.

(* nat maps with unit range are just finite nat sets *)
(* introduce a special name for that *)

Module NatFinSet.
Definition natfinset := union_map [ordType of nat] unit.
Definition natfinsetSPCMMixin := natmapSPCMMixin unit.
Canonical natfinsetSPCM := Eval hnf in SPCM natfinset natfinsetSPCMMixin.

Module Exports.
Notation natfinset := natfinset.
Notation natfinsetSPCMMixin := natfinsetSPCMMixin.
Canonical natfinsetSPCM.
End Exports.

End NatFinSet.

Export NatFinSet.Exports.




