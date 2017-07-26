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

Record Transmission := mkT {to: nid; msg: Message}.
Definition NullTransmission := mkT 0 NullMsg.

Definition ToSend := seq Transmission.
Definition emitZero : ToSend := [:: NullTransmission].
Definition emitOne (trans : Transmission) : ToSend := [:: trans].
Definition emitMany (trsms : ToSend) := trsms.

Definition emitOneToOne (to : nid) (msg : Message) : ToSend := [:: mkT to msg].
Definition emitManyToOne (to : nid) (msgs : seq Message) : ToSend :=
  [seq (mkT to msg) | msg <- msgs].


Section Node. (* Node behaviour *)

Record State :=
  Node {
    id : nid;
    peers : peers_t;
  }.

Definition Init (n : nid) : State := Node n [:: n].
  
Definition StepFun := State -> Message -> (State * ToSend).

Definition step : StepFun :=
  fun (st: State) (msg: Message) =>
    match st with
    | Node n prs =>
      match msg with
      | Connect peer => pair (Node n (undup (peer :: prs))) emitZero
      | Addr _ knownPeers =>
        let: newP := [seq x <- knownPeers | x \notin prs] in
        let: connects := [seq mkT p (Connect n) | p <- newP] in
          pair (Node n (undup (prs ++ newP))) (emitMany(connects))
      | _ => pair st emitZero
      end
    end.

Compute step (Init 0) (Addr 1 [:: 0; 1; 2; 4]).
Compute step (fst (step (Init 0) (Connect 1))) (Addr 1 [:: 0; 1; 2; 4]).

Lemma id_constant :
  forall (s1 : State) (m : Message), let: s2 := (step s1 m).1 in
    id s1 = id s2.
Proof.
case=> n1 p1 []; by [].
Qed.

Lemma peers_nodups :
  forall (s1 : State) (m : Message), let: s2 := (step s1 m).1 in
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
    
End Node.
