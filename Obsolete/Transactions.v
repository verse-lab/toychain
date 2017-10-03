(* Old axioms on transactions *)

(* (* Axioms and other properties *) *)
(* Axiom tpExtend_validAndConsistent : *)
(*   forall (bt : BlockTree) (pool : TxPool) (tx : Transaction), *)
(*     tx \in (tpExtend pool bt tx) -> (txValid tx (btChain bt)). *)

(* Axiom tpExtend_withDup_noEffect : *)
(*   forall (bt : BlockTree) (pool : TxPool) (tx : Transaction), *)
(*     tx \in pool -> (tpExtend pool bt tx) = pool. *)

(* Axiom VAF_inj : *)
(*   forall (v v' : VProof) (ts : Timestamp) (bc1 bc2 : Blockchain), *)
(*     VAF v ts bc1 -> VAF v' ts bc2 -> v == v' /\ bc1 == bc2. *)
