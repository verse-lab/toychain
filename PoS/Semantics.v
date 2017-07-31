From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
Require Import Protocol.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Network semantics *)
Section PacketEqType.

Definition eqpkt a b :=
  ((src a) == (src b)) && ((dst a) == (dst b)) &&
  match (msg a), (msg b) with
  | NullMsg, NullMsg => true
  | NullMsg, _ => false
  | Addr idA prsA, Addr idB prsB => (idA == idB) && (prsA == prsB)
  | Addr _ _, _ => false
  | Connect idA, Connect idB => (idA == idB)
  | Connect _, _ => false
  end.

Lemma eqpktP : Equality.axiom eqpkt.
Proof.
case=>sa da ma [sb] db mb; rewrite/eqpkt/=.
case P1: (sa == sb)=>/=; last by constructor 2; case=>/eqP; rewrite P1.
case P2: (da == db)=>/=; last by constructor 2; case=> _ /eqP; rewrite P2.
move/eqP: P1=>P1; move/eqP: P2=>P2; subst sb db.
case: ma=>[|n p|n].
- case: mb=>//[|n' p'|n']; do? [by constructor 2]; by constructor 1.  
- case: mb=>//[|n' p'|n']; do? [by constructor 2].
  case B: ((n == n') && (p == p')).
  - by case/andP: B=>/eqP<-/eqP<-; constructor 1.
  by case/Bool.andb_false_elim: B=>B; constructor 2; case; move/eqP: B.
case: mb=>//[|n' p'|n']; do? [by constructor 2].
case B: (n == n'); first by case/eqP:B=><-; constructor 1.
by constructor 2; case=>E; subst n'; rewrite eqxx in B.
Qed.

Canonical Packet_eqMixin := Eval hnf in EqMixin eqpktP.
Canonical Packet_eqType := Eval hnf in EqType Packet Packet_eqMixin.

End PacketEqType.

Definition PacketSoup := seq Packet.

Definition StateMap := union_map [ordType of nid] State.

Record World :=
  mkW {
    localState : StateMap;
    inFlightMsgs : PacketSoup;
    }.

Check dst.

Inductive reliable_step (w w' : World) : Prop :=
| step_msg (p : Packet) (st st' : State) (ms : ToSend) of
      p \in inFlightMsgs w &
      find (dst p) (localState w) = Some st &
      updS st (msg p) = (st', ms) &      
      w' = mkW (upd (dst p) st' (localState w))
               (ms ++ seq.rem p (inFlightMsgs w)).
