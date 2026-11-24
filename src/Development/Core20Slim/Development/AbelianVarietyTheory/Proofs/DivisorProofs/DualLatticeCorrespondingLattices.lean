module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch.Transport

theorem dualLat_latCorr {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
    {D D₂ : Type} [Fintype D] [Fintype D₂] (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) : LatCorr j cD (dualLat Λ) (dualLat Λ₂) := by
  have key : ∀ y x : D → k, (fun c => j (y (cD c))) ⬝ᵥ (fun c => j (x (cD c))) = j (y ⬝ᵥ x) := by
    intro y x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul]
    exact Fintype.sum_equiv cD _ _ fun c => rfl
  intro y
  rw [mem_dualLat, mem_dualLat]
  constructor
  · intro H x hx
    have := H _ ((h x).2 hx)
    rw [key] at this
    exact (hj.2.2 _).1 this
  · intro H x₂ hx₂
    set x : D → k := fun d => j.symm (x₂ (cD.symm d)) with hxdef
    have hx : (fun c => j (x (cD c))) = x₂ := by
      funext c; simp [x]
    rw [← hx] at hx₂ ⊢
    rw [key]
    exact (hj.2.2 _).2 (H x ((h x).1 hx₂))

end GlobalTheory.PureMatch.Transport
