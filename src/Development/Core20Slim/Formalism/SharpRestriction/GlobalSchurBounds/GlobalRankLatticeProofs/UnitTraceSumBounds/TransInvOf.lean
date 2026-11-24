module

public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.IdealLattice
public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.SigmaStarUniq
public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LemmaTwoThreeOfSiegelBound
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

theorem lamOf_lat (HI : IdealLattice) (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 ∧ lamOf D cc δ = lat2 w₁ w₂ := by
  have hd : D.host.d ≠ 0 := by
    intro h0
    have hs : D.host.sqd = 0 := by
      have h := D.host.sqd_sq
      rw [h0] at h
      simp at h
      exact h
    have hK : D.host.K = ⊥ := by
      show IntermediateField.adjoin ℚ {D.host.sqd} = ⊥
      rw [hs]
      exact IntermediateField.adjoin_simple_eq_bot_iff.mpr (zero_mem _)
    have h1 := (IntermediateField.finrank_eq_one_iff).mpr hK
    have h2 := Formalism.HC.HostRaw.finrank_K (H := D.host.toHostRaw)
    omega
  have hreal : IsEmpty (D.host.K →+* ℝ) := by
    refine ⟨fun f => ?_⟩
    have hs : (⟨D.host.sqd, Formalism.HC.HostRaw.sqd_mem_K (H := D.host.toHostRaw)⟩ : D.host.K) ^ 2 =
        -((D.host.d : ℕ) : D.host.K) := by
      apply Subtype.ext
      simpa using D.host.sqd_sq
    have h2 := congrArg f hs
    rw [map_pow, map_neg, map_natCast] at h2
    have h3 := sq_nonneg (f ⟨D.host.sqd, Formalism.HC.HostRaw.sqd_mem_K (H := D.host.toHostRaw)⟩)
    have h4 : (0 : ℝ) < (D.host.d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
    linarith
  obtain ⟨⟨w₁, w₂, hw, heq⟩, -⟩ :=
    HI D.host.K (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) (Formalism.HC.HostRaw.finrank_K (H := D.host.toHostRaw))
      hreal cc δ hc hδ
  exact ⟨w₁, w₂, hw, heq⟩

theorem delta_ne (HI : IdealLattice) (HD : DiscrNe) (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 := by
  obtain ⟨w₁, w₂, hw, hL⟩ := lamOf_lat HI D cc hc 1 one_ne_zero
  intro h0
  have h12 : δ ^ 12 = discr (lamOf D cc 1) := hδ
  rw [h0, hL] at h12
  exact HD w₁ w₂ hw (by simpa using h12.symm)

end Formalism.MainNotions.Ext
