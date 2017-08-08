From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Relations.
Require Import Protocol Blockchain States.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Semantics.

(* Number of nodes *)
Definition PacketSoup := seq Packet.

Record World :=
  mkW {
    localState : StateMap;
    inFlightMsgs : PacketSoup;
    consumedMsgs : PacketSoup;
  }.

(* Network semantics *)

(* Don't you worry about uniqueness of the messages? *)
Inductive system_step (w w' : World) : Prop :=
| Idle of w = w'

| Deliver (p : Packet) (st : State) of
      p \in inFlightMsgs w &
      find (dst p) (localState w) = Some st &
      let: (st', ms) := procMsg st (msg p) in
      w' = mkW (upd (dst p) st' (localState w))
               (ms ++ seq.rem p (inFlightMsgs w))
               (rcons (consumedMsgs w) p)

| Intern (proc : nid) (t : InternalTransition) (st : State) of
      find proc (localState w) = Some st &
      let: (st', ms) := procInt st t in
      w' = mkW (upd proc st' (localState w))
               (ms ++ (inFlightMsgs w))
               (consumedMsgs w).

Definition system_step_star := clos_refl_trans_n1 _ system_step.

Definition reachable (w w' : World) := system_step_star w w'.

(* TODO: define a relation that "reconstructs" an "ideal" blockchain *)
(* from a given world, and prove its properties (e.g., functionality, *)
(* meaning that one world corresponds to one blobkchain *)
(* precisely). This might require to state additional "coherence" *)
(* properties of the world, such as block-trees of the majority of
involved peers are not _too different_. *)

Variable N : nat.

Definition initWorld := mkW (initState N) [::] [::].

Definition holds (n : nid) (w : World) (cond : State -> Prop) :=
  forall (st : State),
    find n (localState w) = Some st -> cond st.

Definition Coh (w : World) :=
  forall (n : nid),
    (* IDs match *)
    holds n w (fun st => id st == n).

Lemma Coh_init : Coh initWorld.
Proof.
move=>n st.
rewrite /initWorld/initState/localState/=.
(* Since the state is constructed inductively, use induction on N *)
elim: N=>//=[|n' Hi].
  (* Using facts about union-maps. *)
- Search _ (find) (Some).
  move/find_some.
  (* Domain of an empty map should be empty, right? *)
  Search _ (dom _) (Unit).
  rewrite dom0.
  (* Fiddling with \in predicate *)
  rewrite inE.
  done.

(* The main induction transition. *)
(* Can we doe somthingabout find of a union? *)
Search _ (find) (_ \+ _).
rewrite findUnL; last first.
- case: validUn; rewrite ?um_validPt ?valid_initState//.
  move=>k; rewrite um_domPt !inE=>/eqP Z; subst k.
  by rewrite dom_initState mem_iota addnC addn1 ltnn andbC. 
case: ifP=>//; rewrite um_domPt inE=>/eqP<-. 
by rewrite um_findPt; case=><-.  
Qed.  


End Semantics.

