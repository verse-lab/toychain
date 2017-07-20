From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype fintype ssrfun seq.
From mathcomp
Require Import finfun.
Require Import Eqdep.
Require Import pred prelude idynamic ordtype domain pcm spcm unionmap heap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*****************************************)
(* Codes for types, small types and pcms *)
(*****************************************)

(* first a data structure of small types *)
(* this is similar to pcms, except it has no operations on it *)
(* i will register a number of types as sets, but, importantly, *)
(* not heaps, which are a larger entity *)

Module SetType.

Section ClassDef.
Structure type : Type := Pack {sort : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition pack := @Pack T.
Definition clone := fun (_ : cT -> T) & phant_id pack cT => pack.
End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation set := type.
Notation SET T := (@pack T).

Notation "[ 'set' 'of' T 'for' C ]" := (@clone T C idfun id)
  (at level 0, format "[ 'set'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'set' 'of' T ]" := (@clone T _ id id)
  (at level 0, format "[ 'set'  'of'  T ]") : form_scope.

End Exports.
End SetType.

Export SetType.Exports.

Canonical unitSet := SET unit.
Canonical natSet := SET nat.
Canonical boolSet := SET bool.
Canonical ptrSet := SET ptr.
Canonical mutexSet := SET mutex.
Canonical optionSet (s : set) := SET (option s).
Canonical seqSet (s : set) := SET (seq s).
Canonical prodSet (s1 s2 : set) := SET (prod s1 s2).
Canonical arrSet (s1 s2 : set) := SET (s1 -> s2).
(* Canonical natfinsetSet := SET natfinset.  *)

(*************************************************)
(* Now the actual codes for types, sets and pcms *)
(*************************************************)

(* so far no need for mutual induction *)
(* It's possible to define this mutually inductively *)
(* but Coq's default induction principles won't account for it *)
(* One has to use Scheme command for that (check CPDT) *)

(* small types *)
Inductive st_code :=
  st_unit | st_nat | st_bool | st_ptr | st_mtx | (* st_natfinset | *) (* nullary *)
  st_option of st_code | st_seq of st_code | (* unary *)
  st_prod of st_code & st_code | st_arr of st_code & st_code. (* binary *)

(* small pcms, unused so far *)
Inductive spcm_code :=
  spcm_unit | spcm_nat | spcm_natmap of st_code | spcm_ptrmap of st_code |
  spcm_prod of spcm_code & spcm_code.

(* general pcm's *)
Inductive pcm_code :=
  pcm_unit | pcm_nat | pcm_mtx | pcm_heap | pcm_natmap of st_code |
  pcm_ptrmap of st_code | pcm_prod of pcm_code & pcm_code.

(* general types *)
Inductive tp_code :=
  tp_unit | tp_nat | tp_bool | tp_ptr | tp_mtx | tp_heap | (* nullary *)
  tp_option of tp_code | tp_seq of tp_code | (* unary *)
  tp_prod of tp_code & tp_code | tp_arr of tp_code & tp_code | (* binary *)
  tp_array of nat & pcm_code | tp_ptrmap of st_code.

Fixpoint st_sort (x : st_code) : set :=
  match x with
  | st_unit => [set of unit]
  | st_nat => [set of nat]
  | st_bool => [set of bool]
  | st_ptr => [set of ptr]
  | st_mtx => [set of mutex]
  (* | st_natfinset => [set of natfinset] *)
  | st_option y => [set of option (st_sort y)]
  | st_seq y => [set of seq (st_sort y)]
  | st_prod y z => [set of (st_sort y * st_sort z)]
  | st_arr y z => [set of st_sort y -> st_sort z]
  end.

Fixpoint spcm_sort (x : spcm_code) : spcm :=
  match x with
  | spcm_unit => unitSPCM
  | spcm_nat => natSPCM
  | spcm_natmap t2 => natmapSPCM (st_sort t2)
  | spcm_ptrmap t2 => ptrmapSPCM (st_sort t2)
  | spcm_prod y z => prodSPCM (spcm_sort y) (spcm_sort z)
  end.

Fixpoint pcm_sort (x : pcm_code) : pcm :=
  match x with
  | pcm_unit => [pcm of unit]
  | pcm_nat => [pcm of nat]
  | pcm_mtx => [pcm of lift [unlifted of mutex]]
  | pcm_heap => [pcm of heap]
  | pcm_natmap t2 => [pcm of union_map nat_ordType (st_sort t2)]
  | pcm_ptrmap t2 => [pcm of union_map ptr_ordType (st_sort t2)]
  | pcm_prod y z => [pcm of pcm_sort y * pcm_sort z]
  end.

Fixpoint tp_sort (x : tp_code) : Type :=
  match x with
  | tp_unit => unit
  | tp_nat => nat
  | tp_bool => bool
  | tp_ptr => ptr
  | tp_mtx => mutex
  | tp_heap => heap
  | tp_option y => option (tp_sort y)
  | tp_seq y => seq (tp_sort y)
  | tp_prod y z => (tp_sort y * tp_sort z)%type
  | tp_arr y z => tp_sort y -> tp_sort z
  | tp_array n z => {ffun 'I_n -> pcm_sort z}
  | tp_ptrmap z => union_map ptr_ordType (st_sort z)
  end.

(* deciding equality on each of these types *)

Fixpoint st_eq x y :=
  match x, y with
  | st_unit, st_unit => true
  | st_nat, st_nat => true
  | st_bool, st_bool => true
  | st_ptr, st_ptr => true
  | st_mtx, st_mtx => true
  (* | st_natfinset, st_natfinset => true *)
  | st_option x1, st_option y1 => st_eq x1 y1
  | st_seq x1, st_seq y1 => st_eq x1 y1
  | st_prod x1 y1, st_prod x2 y2 =>
      st_eq x1 x2 && st_eq y1 y2
  | st_arr x1 y1, st_arr x2 y2 =>
      st_eq x1 x2 && st_eq y1 y2
  | _, _ => false
  end.

Fixpoint spcm_eq x y :=
  match x, y with
  | spcm_unit, spcm_unit => true
  | spcm_nat, spcm_nat => true
  | spcm_natmap t1, spcm_natmap t2 => st_eq t1 t2
  | spcm_ptrmap t1, spcm_ptrmap t2 => st_eq t1 t2
  | spcm_prod x1 y1, spcm_prod x2 y2 =>
      spcm_eq x1 x2 && spcm_eq y1 y2
  | _, _ => false
  end.

Fixpoint pcm_eq x y :=
  match x, y with
  | pcm_unit, pcm_unit => true
  | pcm_nat, pcm_nat => true
  | pcm_mtx, pcm_mtx => true
  | pcm_heap, pcm_heap => true
  | pcm_natmap t1, pcm_natmap t2 => st_eq t1 t2
  | pcm_ptrmap t1, pcm_ptrmap t2 => st_eq t1 t2
  | pcm_prod x1 y1, pcm_prod x2 y2 =>
      pcm_eq x1 x2 && pcm_eq y1 y2
  | _, _ => false
  end.

Fixpoint tp_eq x y :=
  match x, y with
  | tp_unit, tp_unit => true
  | tp_nat, tp_nat => true
  | tp_bool, tp_bool => true
  | tp_ptr, tp_ptr => true
  | tp_mtx, tp_mtx => true
  | tp_heap, tp_heap => true
  | tp_option x1, tp_option y1 => tp_eq x1 y1
  | tp_seq x1, tp_seq y1 => tp_eq x1 y1
  | tp_prod x1 y1, tp_prod x2 y2 =>
      tp_eq x1 x2 && tp_eq y1 y2
  | tp_arr x1 y1, tp_arr x2 y2 =>
      tp_eq x1 x2 && tp_eq y1 y2
  | tp_array n1 y1, tp_array n2 y2 =>
      (n1 == n2) && (pcm_eq y1 y2)
  | tp_ptrmap y1, tp_ptrmap y2 => st_eq y1 y2
  | _, _ => false
  end.


(* all are equality types *)

Lemma st_eqP : Equality.axiom st_eq.
Proof.
elim;
(* nullaries *)
try by [case; constructor];
(* unaries *)
try by
  [move=>x IH; case; try by [constructor];
   move=>y; apply: iffP (IH y) _ _; [move=>-> | case]];
(* binaries *)
by [move=>x1 IHx y1 IHy; case; try by [constructor];
    move=>x2 y2 /=; apply: iffP andP _ _;
    case; move/IHx=>->; move/IHy=>->].
Qed.

Lemma spcm_eqP : Equality.axiom spcm_eq.
Proof.
elim;
try by [case; constructor].
- move=>t; case=>/=; try constructor=>//; move=>y.
  by case: st_eqP=>[->|H]; constructor=>//; case.
- move=>t; case=>/=; try constructor=>//; move=>y.
  by case: st_eqP=>[->|H]; constructor=>//; case.
by [move=>x1 IHx y1 IHy; case; try by [constructor];
    move=>x2 y2 /=; apply: iffP andP _ _;
    case; move/IHx=>->; move/IHy=>->].
Qed.

Lemma pcm_eqP : Equality.axiom pcm_eq.
Proof.
elim;
try by [case; constructor].
- move=>t; case=>/=; try constructor=>//; move=>y.
  by case: st_eqP=>[->|H]; constructor=>//; case.
- move=>t; case=>/=; try constructor=>//; move=>y.
  by case: st_eqP=>[->|H]; constructor=>//; case.
by [move=>x1 IHx y1 IHy; case; try by [constructor];
    move=>x2 y2 /=; apply: iffP andP _ _;
    case; move/IHx=>->; move/IHy=>->].
Qed.

Lemma tp_eqP : Equality.axiom tp_eq.
Proof.
elim;
(* nullaries *)
try by [case; constructor];
(* unaries *)
try by
  [move=>x IH; case; try by [constructor];
   move=>y; apply: iffP (IH y) _ _; [move=>-> | case]];
(* binaries *)
try by [move=>x1 IHx y1 IHy; case; try by [constructor];
    move=>x2 y2 /=; apply: iffP andP _ _;
    case; move/IHx=>->; move/IHy=>->].
(* array case *)
move=>n1 p1 []; try by [constructor].
move=>n2 p2 /=; case: eqP=>[->|H]; last by constructor; case.
by case: pcm_eqP=>[->|H]; constructor=>//; case.
(* map case *)
move=>s1 []; try by [constructor].
by move=>s2 /=; case: st_eqP=>[->|H]; constructor=>//; case.
Qed.

(* declaration of equality structures *)
Definition st_code_eqMixin := EqMixin st_eqP.
Canonical st_code_eqType := EqType st_code st_code_eqMixin.

Definition spcm_code_eqMixin := EqMixin spcm_eqP.
Canonical spcm_code_eqType := EqType spcm_code spcm_code_eqMixin.

Definition pcm_code_eqMixin := EqMixin pcm_eqP.
Canonical pcm_code_eqType := EqType pcm_code pcm_code_eqMixin.

Definition tp_code_eqMixin := EqMixin tp_eqP.
Canonical tp_code_eqType := EqType tp_code tp_code_eqMixin.

(*********************************)
(* Now the structures for coding *)
(*********************************)

Module Code.

Structure mixin_of (T : Type) := Mixin {
  code_dom_op : eqType;
  encode_op : code_dom_op -> T;
  to_type_op : T -> Type}.

Section ClassDef.

Notation class_of := mixin_of (only parsing).

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.

Definition pack c := @Pack T c T.
Definition clone := fun c & cT -> T & phant_id (pack c) cT => pack c.

Definition code_dom := code_dom_op class.
Definition encode := @encode_op _ class.
Definition to_type := to_type_op class.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation code := type.
Notation codeMixin c i := (@Mixin _ c i).
Notation Code T m := (@pack T m).

Notation code_dom := code_dom.
Notation encode := encode.
Notation to_type := to_type.

Implicit Arguments to_type [cT].
Implicit Arguments encode [cT].

Prenex Implicits to_type encode.

Notation "[ 'codeMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'codeMixin'  'of'  T ]") : form_scope.
Notation "[ 'code' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'code'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'code' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'code'  'of'  T ]") : form_scope.

End Exports.

End Code.

Export Code.Exports.


(* each of the above datatypes is a code according to above definition *)

Definition set_codeMixin := codeMixin st_code_eqType st_sort SetType.sort.
Canonical setCode := Code set set_codeMixin.

Definition spcm_codeMixin := codeMixin spcm_code_eqType spcm_sort SPCM.sort.
Canonical spcmCode := Code spcm spcm_codeMixin.

Definition pcm_codeMixin := codeMixin pcm_code_eqType pcm_sort PCM.sort.
Canonical pcmCode := Code pcm pcm_codeMixin.

Definition type_codeMixin := codeMixin tp_code_eqType tp_sort id.
Canonical typeCode := Code Type type_codeMixin.

(*********************************************)
(* Computing code instance for a PCM or type *)
(*********************************************)

(* this is a canonical structure setup that inverts the interp function. *)
(* important so that we avoid excesive pcm_code or tp_code annotations. *)

Module Encoded.
Section Encoded.
Variable C : code.

Structure mixin_of (v : C) := Mixin {
  decode_op : code_dom C;
  _ : encode decode_op = v}.

Section ClassDef.

Notation class_of := mixin_of (only parsing).

Structure type : Type := Pack {sort : C; _ : class_of sort; _ : C}.
Local Coercion sort : type >-> Code.sort.

Variables (v : C) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.

Definition pack c := @Pack v c v.

Definition clone :=
  fun c & to_type cT -> to_type v & phant_id (pack c) cT => pack c.

Definition decode := decode_op class.

End ClassDef.
End Encoded.

Module Exports.
Coercion sort : type >-> Code.sort.
Notation encoded := type.
Notation encodeMixin := Mixin.
Notation Encode C v m := (@pack C v m).

Notation decode := decode.

Implicit Arguments encodeMixin [].

Section Lemmas.
Variable C : code.
Implicit Type U : encoded C.

(* the next lemma is problematic to use in practice *)
(* as the rewriting gets in trouble with dependencies *)
(* the solution is to break up U, just like in proof below *)

Lemma encdecE U : encode (decode U) = U.
Proof. by case: U=>tp []. Qed.

Lemma decode_inj U1 U2 : decode U1 = decode U2 -> U1 = U2 :> C.
Proof.
case: U1=>s1 [dec1 pf1 t1]; case: U2=>s2 [dec2 pf2 t2] /=.
by rewrite /decode /= -pf1 -pf2=>->.
Qed.

Definition code_dyn U (v : to_type U) :=
  @idyn (code_dom C) (to_type \o encode) (decode U)
                     (icoerce to_type v (esym (encdecE U))).

(* every idynamic can be recast into a code_dyn form *)

Section CodeEta.
Variable u : idynamic (to_type \o @encode C).

Definition code_enc : encoded C :=
  let: v := encode (idyn_tp u) in
  let: m := @encodeMixin C v (idyn_tp u) (erefl _) in
    Encode C v m.

Definition code_val : to_type code_enc := idyn_val u.

Lemma code_eta : u = code_dyn code_val.
Proof. by rewrite -{1}(idyn_eta u); apply: idynE=>// pf; rewrite !ieqc. Qed.

End CodeEta.

End Lemmas.

Notation "[ 'encodedMixin' C 'for' v ]" := (@class C _ : @mixin_of C v)
  (at level 0, format "[ 'encodedMixin'  C  'for'  v ]") : form_scope.
Notation "[ 'encoded' C 'of' v 'for' R ]" := (@clone C v R _ idfun id)
  (at level 0, format "[ 'encoded'  C  'of'  v  'for'  R ]") : form_scope.
Notation "[ 'encoded' C 'of' v ]" := (@clone C v _ _ idfun id)
  (at level 0, format "[ 'encoded'  C  'of'  v ]") : form_scope.

End Exports.

End Encoded.

Export Encoded.Exports.

Definition encoded_set := encoded setCode.
Definition encodeMixinST := encodeMixin setCode.
Definition EncodeST v m : encoded_set := @Encoded.pack setCode v m.
Implicit Arguments encodeMixinST [].
Implicit Arguments EncodeST [].

Definition encoded_spcm := encoded spcmCode.
Definition encodeMixinSPCM := encodeMixin spcmCode.
Definition EncodeSPCM v m : encoded_spcm := @Encoded.pack spcmCode v m.
Implicit Arguments encodeMixinSPCM [].
Implicit Arguments EncodeSPCM [].

Definition encoded_pcm := encoded pcmCode.
Definition encodeMixinPCM := encodeMixin pcmCode.
Definition EncodePCM v m : encoded_pcm := @Encoded.pack pcmCode v m.
Implicit Arguments encodeMixinPCM [].
Implicit Arguments EncodePCM [].

Definition encoded_type := encoded typeCode.
Definition encodeMixinTP := encodeMixin typeCode.
Definition EncodeTP v m : encoded_type := @Encoded.pack typeCode v m.
Implicit Arguments encodeMixinTP [].
Implicit Arguments EncodeTP [].

(* add the explicit coercions *)

Definition encoded_sort_set : encoded_set -> set :=
  fun U => Encoded.sort U.
Coercion encoded_sort_set : encoded_set >-> set.

Definition encoded_sort_spcm : encoded_spcm -> spcm :=
  fun U => Encoded.sort U.
Coercion encoded_sort_spcm : encoded_spcm >-> spcm.

Definition encoded_sort_pcm : encoded_pcm -> pcm :=
  fun U => Encoded.sort U.
Coercion encoded_sort_pcm : encoded_pcm >-> pcm.

Definition encoded_sort_type : encoded_type -> Type :=
  fun U => Encoded.sort U.
Coercion encoded_sort_type : encoded_type >-> Sortclass.

(* Can I coerce spcms to pcms? *)

Fixpoint spcm_to_pcm (x : spcm_code) : pcm_code :=
  match x with
  | spcm_unit => pcm_unit
  | spcm_nat => pcm_nat
  | spcm_natmap t2 => pcm_natmap t2
  | spcm_ptrmap t2 => pcm_ptrmap t2
  | spcm_prod y z => pcm_prod (spcm_to_pcm y) (spcm_to_pcm z)
  end.

Lemma spcm_pcm_pf (V : encoded_spcm) :
        @encode pcmCode (spcm_to_pcm (decode V)) = V.
Proof.
case: V=>V [d E /=] s; rewrite /decode /= -{}E /encode.
elim: d=>[||d|d|/= s1 -> s2 ->];
by congr PCM.pack; congr PCM.Mixin; try apply: proof_irrelevance.
Qed.

Definition spcm_pcm_encodedMixin (V : encoded_spcm) :=
  encodeMixinPCM V (spcm_to_pcm (decode V)) (spcm_pcm_pf V).
Canonical spcm_pcm_Encoded (V : encoded_spcm) :=
  EncodePCM V (spcm_pcm_encodedMixin V).

Coercion spcm_pcm_Encoded : encoded_spcm >-> encoded_pcm.

(* Moving on; special notation *)

Definition pcm_dyn (U : encoded_pcm) (v : U) := @code_dyn pcmCode U v.

Section PCMEta.
Variable u : idynamic (to_type \o pcm_sort).

Definition pcm_enc : encoded_pcm := @code_enc pcmCode u.
Definition pcm_val : pcm_enc := @code_val pcmCode u.
Definition pcm_eta : u = pcm_dyn pcm_val := @code_eta pcmCode u.

End PCMEta.

(****************************)
(* inversion table for sets *)
(****************************)

Definition unit_st_encodedMixin := encodeMixinST unitSet st_unit (erefl _).
Canonical unit_st_Encoded := EncodeST unitSet unit_st_encodedMixin.

Definition nat_st_encodedMixin := encodeMixinST natSet st_nat (erefl _).
Canonical nat_st_Encoded := EncodeST natSet nat_st_encodedMixin.

Definition bool_st_encodedMixin := encodeMixinST boolSet st_bool (erefl _).
Canonical bool_st_Encoded := EncodeST boolSet bool_st_encodedMixin.

Definition ptr_st_encodedMixin := encodeMixinST ptrSet st_ptr (erefl _).
Canonical ptr_st_Encoded := EncodeST ptrSet ptr_st_encodedMixin.

Definition mtx_st_encodedMixin := encodeMixinST mutexSet st_mtx (erefl _).
Canonical mtx_st_Encoded := EncodeST mutexSet mtx_st_encodedMixin.

(*
Definition natfinset_st_encodedMixin :=
  encodeMixinST natfinsetSet st_natfinset (erefl _).
Canonical natfinset_st_Encoded := EncodeST natfinsetSet natfinset_st_encodedMixin.
*)

Lemma option_st_pf (U : encoded_set) :
        @encode setCode (st_option (decode U)) = optionSet U.
Proof. by rewrite /decode; case: U=>st [/= dp <-]. Qed.

Definition option_st_encodedMixin (U : encoded_set) :=
  encodeMixin setCode (optionSet U) (st_option (decode U)) (option_st_pf U).
Canonical option_st_Encoded (U : encoded_set) :=
  EncodeST (optionSet U) (option_st_encodedMixin U).

Lemma seq_st_pf (U : encoded_set) :
        @encode setCode (st_seq (decode U)) = seqSet U.
Proof. by rewrite /decode; case: U=>st [/= dp <-]. Qed.

Definition seq_st_encodedMixin (U : encoded_set) :=
  encodeMixin setCode (seqSet U) (st_seq (decode U)) (seq_st_pf U).
Canonical seq_st_Encoded (U : encoded_set) :=
  EncodeST (seqSet U) (seq_st_encodedMixin U).

Lemma prod_st_pf (U1 U2 : encoded_set) :
        @encode setCode (st_prod (decode U1) (decode U2)) = prodSet U1 U2.
Proof. by rewrite /decode; case: U1 U2=>t1 [/= ? <-] _ [t2 [/= ? <-]]. Qed.

Definition prod_st_encodedMixin (U1 U2 : encoded_set) :=
  encodeMixinST (prodSet U1 U2)
                (st_prod (decode U1) (decode U2)) (prod_st_pf U1 U2).
Canonical prod_st_Encoded (U1 U2 : encoded_set) :=
  EncodeST (prodSet U1 U2) (prod_st_encodedMixin U1 U2).

(* this one is kinda pointless since we can't trigger inference of lambda's *)
(* so functions will have to be decorated with their types by hand *)

Lemma arr_st_pf (U1 U2 : encoded_set) :
        @encode setCode (st_arr (decode U1) (decode U2)) = arrSet U1 U2.
Proof. by rewrite /decode; case: U1 U2=>t1 [/= ? <-] _ [t2 [/= ? <-]]. Qed.

Definition arr_st_encodedMixin (U1 U2 : encoded_set) :=
  encodeMixinST (arrSet U1 U2) (st_arr (decode U1) (decode U2)) (arr_st_pf U1 U2).
Canonical arr_st_Encoded (U1 U2 : encoded_set) :=
  EncodeST (arrSet U1 U2) (arr_st_encodedMixin U1 U2).

(*
Notation "[ 'encoded_set' 'of' v ]" :=
  ([encoded setCode of [set of v]])
  (at level 0, format "[ 'encoded_set'  'of'  v ]") : form_scope.
*)

Definition set_clone v cT c b1 b2 : encoded_set :=
  @Encoded.clone setCode v cT c b1 b2.

Notation "[ 'encoded_set' 'of' v ]" := (@set_clone [set of v] _ _ idfun id)
  (at level 0, format "[ 'encoded_set'  'of'  v ]") : form_scope.

(*****************************)
(* inversion table for types *)
(*****************************)

Definition unit_tp_encodedMixin := encodeMixinTP (unit : Type) tp_unit (erefl _).
Canonical unit_tp_Encoded := EncodeTP unit unit_tp_encodedMixin.

Definition nat_tp_encodedMixin := encodeMixinTP nat tp_nat (erefl _).
Canonical nat_tp_Encoded := EncodeTP nat nat_tp_encodedMixin.

Definition bool_tp_encodedMixin := encodeMixinTP bool tp_bool (erefl _).
Canonical bool_tp_Encoded := EncodeTP bool bool_tp_encodedMixin.

Definition ptr_tp_encodedMixin := encodeMixinTP ptr tp_ptr (erefl _).
Canonical ptr_tp_Encoded := EncodeTP ptr ptr_tp_encodedMixin.

Definition mtx_tp_encodedMixin := encodeMixinTP mutex tp_mtx (erefl _).
Canonical mtx_tp_Encoded := EncodeTP mutex mtx_tp_encodedMixin.

Definition heap_tp_encodedMixin := encodeMixinTP heap tp_heap (erefl _).
Canonical heap_tp_Encoded := EncodeTP heap heap_tp_encodedMixin.

Lemma option_tp_pf (U : encoded_type) :
        @encode typeCode (tp_option (decode U)) = option U.
Proof. by rewrite /decode; case: U=>tp [/= dp <-]. Qed.

Definition option_tp_encodedMixin (U : encoded_type) :=
  encodeMixin typeCode (option U) (tp_option (decode U)) (option_tp_pf U).
Canonical option_tp_Encoded (U : encoded_type) :=
  EncodeTP (option U) (option_tp_encodedMixin U).

Lemma seq_tp_pf (U : encoded_type) :
        @encode typeCode (tp_seq (decode U)) = seq U.
Proof. by rewrite /decode; case: U=>tp [/= dp <-]. Qed.

Definition seq_tp_encodedMixin (U : encoded_type) :=
  encodeMixin typeCode (seq U) (tp_seq (decode U)) (seq_tp_pf U).
Canonical seq_tp_Encoded (U : encoded_type) :=
  EncodeTP (seq U) (seq_tp_encodedMixin U).

Lemma prod_tp_pf (U1 U2 : encoded_type) :
        @encode typeCode (tp_prod (decode U1) (decode U2)) = prod U1 U2.
Proof. by rewrite /decode; case: U1 U2=>t1 [/= ? <-] _ [t2 [/= ? <-]]. Qed.

Definition prod_tp_encodedMixin (U1 U2 : encoded_type) :=
  encodeMixinTP (prod U1 U2)
                (tp_prod (decode U1) (decode U2)) (prod_tp_pf U1 U2).
Canonical prod_tp_Encoded (U1 U2 : encoded_type) :=
  EncodeTP (prod U1 U2) (prod_tp_encodedMixin U1 U2).

(* this one is kinda pointless since we can't trigger inference of lambda's *)
(* so functions will have to be decorated with their types by hand *)

Lemma arr_tp_pf (U1 U2 : encoded_type) :
        @encode typeCode (tp_arr (decode U1) (decode U2)) = (U1 -> U2).
Proof. by rewrite /decode; case: U1 U2=>t1 [/= ? <-] _ [t2 [/= ? <-]]. Qed.

Definition arr_tp_encodedMixin (U1 U2 : encoded_type) :=
  encodeMixinTP (U1 -> U2) (tp_arr (decode U1) (decode U2)) (arr_tp_pf U1 U2).
Canonical arr_tp_Encoded (U1 U2 : encoded_type) :=
  EncodeTP (U1 -> U2) (arr_tp_encodedMixin U1 U2).

Lemma array_tp_pf (n : nat) (U : encoded_pcm) :
        @encode typeCode (tp_array n (decode U)) = {ffun 'I_n -> U}.
Proof. by rewrite /decode; case: U=>t [/= d <- _]. Qed.

Definition array_tp_encodedMixin n (U : encoded_pcm) :=
  encodeMixinTP {ffun 'I_n -> U}
                (tp_array n (decode U)) (array_tp_pf n U).
Canonical array_tp_Encoded n (U : encoded_pcm) :=
  EncodeTP {ffun 'I_n -> U} (array_tp_encodedMixin n U).

Lemma ptrmap_tp_pf (V : encoded_set) :
        @encode typeCode (tp_ptrmap (decode V)) = union_map ptr_ordType V.
Proof. by rewrite /decode; case: V=>t [/= d <- _]. Qed.

Definition ptrmap_tp_encodedMixin (V : encoded_set) :=
  encodeMixinTP (union_map ptr_ordType V) (tp_ptrmap (decode V))
                (ptrmap_tp_pf V).
Canonical ptrmap_tp_Encoded (V : encoded_set) :=
  EncodeTP (union_map ptr_ordType V) (ptrmap_tp_encodedMixin V).

(*
Notation "[ 'encoded_type' 'of' v ]" :=
  ([encoded typeCode of v])
  (at level 0, format "[ 'encoded_type'  'of'  v ]") : form_scope.
*)

Definition type_clone v cT c b1 b2 : encoded_type :=
  @Encoded.clone typeCode v cT c b1 b2.

Notation "[ 'encoded_type' 'of' v ]" := (@type_clone v _ _ idfun id)
  (at level 0, format "[ 'encoded_type'  'of'  v ]") : form_scope.

(****************************)
(* inversion table for pcms *)
(****************************)

Definition unit_pcm_encodedMixin := encodeMixinPCM unitPCM pcm_unit (erefl _).
Canonical unit_pcm_Encoded := EncodePCM unitPCM unit_pcm_encodedMixin.

Definition nat_pcm_encodedMixin := encodeMixinPCM natPCM pcm_nat (erefl _).
Canonical nat_pcm_Encoded := EncodePCM natPCM nat_pcm_encodedMixin.

Definition mtx_pcm_encodedMixin :=
  encodeMixinPCM (liftPCM mutexUnlifted) pcm_mtx (erefl _).
Canonical mtx_pcm_Encoded :=
  EncodePCM (liftPCM mutexUnlifted) mtx_pcm_encodedMixin.

Definition heap_pcm_encodedMixin := encodeMixinPCM heapPCM pcm_heap (erefl _).
Canonical heap_pcm_Encoded := EncodePCM heapPCM heap_pcm_encodedMixin.

Lemma natmap_pcm_pf (V : encoded_set) :
        @encode pcmCode (pcm_natmap (decode V)) = union_mapPCM nat_ordType V.
Proof. by rewrite /decode; case: V=>_ [/= ? <-]. Qed.

Definition natmap_pcm_encodedMixin (V : encoded_set) :=
  encodeMixinPCM (union_mapPCM nat_ordType V) (pcm_natmap (decode V))
                 (natmap_pcm_pf V).
Canonical natmap_pcm_Encoded (V : encoded_set) :=
  EncodePCM (union_mapPCM nat_ordType V) (natmap_pcm_encodedMixin V).

Lemma ptrmap_pcm_pf (V : encoded_set) :
        @encode pcmCode (pcm_ptrmap (decode V)) = union_mapPCM ptr_ordType V.
Proof. by rewrite /decode; case: V=>_ [/= ? <-]. Qed.

Definition ptrmap_pcm_encodedMixin (V : encoded_set) :=
  encodeMixinPCM (union_mapPCM ptr_ordType V) (pcm_ptrmap (decode V))
                 (ptrmap_pcm_pf V).
(* this one overlaps with natmap, so i have to assign it by hand *)
(* it can't be canonical *)
(* this should be fixed by assigning dedicated names to these *)
(* unionmap types; e.g. specifically like natmap and ptrmap *)
Definition ptrmap_pcm_Encoded (V : encoded_set) :=
  EncodePCM (union_mapPCM ptr_ordType V) (ptrmap_pcm_encodedMixin V).

Lemma prod_pcm_pf (U1 U2 : encoded_pcm) :
        @encode pcmCode (pcm_prod (decode U1) (decode U2)) = prodPCM U1 U2.
Proof. by rewrite /decode; case: U1 U2=>t1 [/= ? <-] _ [t2 [/= ? <-]]. Qed.

Definition prod_pcm_encodedMixin (U1 U2 : encoded_pcm) :=
  encodeMixinPCM (prodPCM U1 U2)
                 (pcm_prod (decode U1) (decode U2)) (prod_pcm_pf U1 U2).
Canonical prod_pcm_Encoded (U1 U2 : encoded_pcm) :=
  EncodePCM (prodPCM U1 U2) (prod_pcm_encodedMixin U1 U2).

(*
Notation "[ 'encoded_pcm' 'of' v ]" :=
  ([encoded pcmCode of [pcm of v]])
  (at level 0, format "[ 'encoded_pcm'  'of'  v ]") : form_scope.
*)

Definition pcm_clone v cT c b1 b2 : encoded_pcm :=
  @Encoded.clone pcmCode v cT c b1 b2.

Notation "[ 'encoded_pcm' 'of' v ]" := (@pcm_clone [pcm of v] _ _ idfun id)
  (at level 0, format "[ 'encoded_pcm'  'of'  v ]") : form_scope.


(*****************************)
(* inversion table for spcms *)
(*****************************)

Definition unit_spcm_encodedMixin :=
  encodeMixinSPCM unitSPCM spcm_unit (erefl _).
Canonical unit_spcm_Encoded := EncodeSPCM unitSPCM unit_spcm_encodedMixin.

Definition nat_spcm_encodedMixin := encodeMixinSPCM natSPCM spcm_nat (erefl _).
Canonical nat_spcm_Encoded := EncodeSPCM natSPCM nat_spcm_encodedMixin.

Lemma natmap_spcm_pf (V : encoded_set) :
        @encode spcmCode (spcm_natmap (decode V)) = natmapSPCM V.
Proof. by rewrite /decode; case: V=>_ [/= ? <-]. Qed.

Definition natmap_spcm_encodedMixin (V : encoded_set) :=
  encodeMixinSPCM (natmapSPCM V) (spcm_natmap (decode V))
                  (natmap_spcm_pf V).
Canonical natmap_spcm_Encoded (V : encoded_set) :=
  EncodeSPCM (natmapSPCM V) (natmap_spcm_encodedMixin V).

Lemma ptrmap_spcm_pf (V : encoded_set) :
        @encode spcmCode (spcm_ptrmap (decode V)) = ptrmapSPCM V.
Proof. by rewrite /decode; case: V=>_ [/= ? <-]. Qed.

Definition ptrmap_spcm_encodedMixin (V : encoded_set) :=
  encodeMixinSPCM (ptrmapSPCM V) (spcm_ptrmap (decode V))
                  (ptrmap_spcm_pf V).
Canonical ptrmap_spcm_Encoded (V : encoded_set) :=
  EncodeSPCM (ptrmapSPCM V) (ptrmap_spcm_encodedMixin V).


Lemma prod_spcm_pf (U1 U2 : encoded_spcm) :
        @encode spcmCode (spcm_prod (decode U1) (decode U2)) = prodSPCM U1 U2.
Proof. by rewrite /decode; case: U1 U2=>t1 [/= ? <-] _ [t2 [/= ? <-]]. Qed.

Definition prod_spcm_encodedMixin (U1 U2 : encoded_spcm) :=
  encodeMixinSPCM (prodSPCM U1 U2)
                  (spcm_prod (decode U1) (decode U2)) (prod_spcm_pf U1 U2).
Canonical prod_spcm_Encoded (U1 U2 : encoded_spcm) :=
  EncodeSPCM (prodSPCM U1 U2) (prod_spcm_encodedMixin U1 U2).

(*
Notation "[ 'encoded_spcm' 'of' v ]" :=
  ([encoded spcmCode of [spcm of v]])
  (at level 0, format "[ 'encoded_spcm'  'of'  v ]") : form_scope.
*)

Definition spcm_clone v cT c b1 b2 : encoded_spcm :=
  @Encoded.clone spcmCode v cT c b1 b2.

Notation "[ 'encoded_spcm' 'of' v ]" := (@spcm_clone [spcm of v] _ _ idfun id)
  (at level 0, format "[ 'encoded_spcm'  'of'  v ]") : form_scope.

(*
Print Canonical Projections.
Check [encoded pcmCode of natPCM].
Check [encoded_spcm of nat].
Check [encoded_set of fset _].
Check [encoded_pcm of heap].
Check [encoded_set of nat].
Check [encoded typeCode of unit].
Check (@code_dyn pcmCode _ 3).
Check (@code_dyn typeCode _ [:: 3]).
Check (@code_dyn pcmCode _ (3, 4)).
Check [encoded_pcm of nat].
Check [encoded_type of nat -> nat].
Check [encoded_type of (union_map ptr_ordType [encoded_set of nat])].

Print Canonical Projections.

Check [encoded_pcm of union_map nat_ordType [encoded_set of bool]].
*)


