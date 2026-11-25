module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.InstSecondCountable
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Sum.Basic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Fin.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.HolDS

theorem blockOrd_finSumFinEquiv (p q : ℕ) :
    GlobalTheory.RealPar.BlockOrd (p := p) (q := q) finSumFinEquiv (fun i => (finSumFinEquiv.symm i).isLeft) := by
  refine ⟨fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) hab
  · have : a < b := hab
    exact (Fin.strictMono_castAdd q) this
  · exact hab.elim
  · exact hab.elim
  · have : a < b := hab
    exact (Fin.strictMono_natAdd p) this

end GlobalTheory.HolDS
