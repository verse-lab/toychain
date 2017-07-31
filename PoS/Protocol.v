From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep pred prelude idynamic ordtype pcm finmap unionmap heap coding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Implementation of PoS protocol as a STS *)
Definition nid := nat.
Definition peers_t := seq nid.

Inductive Message :=
  | NullMsg
  | Addr of nid & peers_t
  | Connect of nid.

Record Packet := mkP {src: nid; dst: nid; msg: Message}.
Definition NullPacket := mkP 0 0 NullMsg.

Definition ToSend := seq Packet.
Definition emitZero : ToSend := [:: NullPacket].
Definition emitOne (packet : Packet) : ToSend := [:: packet].
Definition emitMany (packets : ToSend) := packets.

Definition emitOneToOne (from to : nid) (msg : Message) := [:: mkP from to msg].
Definition emitManyToOne (from to : nid) (msgs : seq Message) :=
  [seq (mkP from to msg) | msg <- msgs].


Section Node. (* Node behaviour *)

Record State :=
  Node {
    id : nid;
    peers : peers_t;
  }.

Definition Init (n : nid) : State := Node n [:: n].
Lemma peers_uniq_init (n : nid) : uniq [::n]. Proof. done. Qed.
  

Definition updS : State -> Message -> (State * ToSend) :=
  fun (st: State) (msg: Message) =>
    match st with
    | Node n prs =>
      match msg with
      | Connect peer => pair (Node n (undup (peer :: prs))) emitZero
      | Addr _ knownPeers =>
        let: newP := [seq x <- knownPeers | x \notin prs] in
        let: connects := [seq mkP n p (Connect n) | p <- newP] in
          pair (Node n (undup (prs ++ newP))) (emitMany(connects))
      | _ => pair st emitZero
      end
    end.

Lemma upd_id_constant :
  forall (s1 : State) (m : Message), let: s2 := (updS s1 m).1 in
    id s1 = id s2.
Proof.
case=> n1 p1 []; by [].
Qed.

Lemma upd_peers_uniq :
  forall (s1 : State) (m : Message), let: s2 := (updS s1 m).1 in
    uniq (peers s1) -> uniq (peers s2).
Proof.
case=> n1 p1 [].
- by [].
- case=> [known | n2 known]; move=> UniqP1; by apply undup_uniq.
- simpl. move=> n2 UniqP1. case B: (n2 \in p1).
  + by apply undup_uniq.
  + rewrite cons_uniq undup_id.
    * rewrite B. by [].
    * by [].
Qed.  


Inductive step (s1 s2 : State) : Prop :=
| Idle of s1 = s2
| RcvMsg (m : Message) of (s2 = (updS s1 m).1).

Lemma id_constant :
  forall (s1 s2 : State),
    step s1 s2 -> id s1 = id s2.
Proof.
move=> s1 s2.
case.
- move=> eq. rewrite eq. by  [].
- move=> m Us. rewrite Us. apply upd_id_constant.
Qed.

Lemma peers_uniq :
  forall (s1 s2 : State),
    uniq (peers s1) -> step s1 s2 -> uniq (peers s2).
Proof.
move=> s1 s2 UniqP1.
case.
- move=> eq. rewrite -eq. by [].
- move=> m Us. rewrite Us. apply upd_peers_uniq. by [].
Qed.

End Node.
