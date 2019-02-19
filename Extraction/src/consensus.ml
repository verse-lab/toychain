open Forests
open Protocol

module Addr = Address.Addr
module ConsensusParams = Impl.ProofOfWork
module ForestImpl = Forests (ConsensusParams)
module ProtocolImpl = Protocol (ConsensusParams) (ForestImpl) (Addr)

