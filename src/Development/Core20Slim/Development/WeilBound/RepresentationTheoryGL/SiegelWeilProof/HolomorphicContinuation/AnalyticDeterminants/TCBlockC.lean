module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCBlockA
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt
public import Init.Prelude
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

def eBq (j : ℕ) : {x // x ∈ blkB (n := n) j} ≃ {x // ¬ x ∈ blkA (n := n) j} :=
  Equiv.subtypeEquivRight (fun x => mem_blkB j x)

def piP (j : ℕ) (σA : Equiv.Perm (blkA (n := n) j)) (τ : Equiv.Perm (blkB (n := n) j)) : Equiv.Perm (Fin n) :=
  Equiv.Perm.subtypeCongr σA ((eBq j).permCongr τ)

end PositivityTheory.Rg.Sw.LVs.TC
