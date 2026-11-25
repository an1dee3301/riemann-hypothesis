module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

noncomputable section

namespace GlobalTheory.Hk3.GramSep

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def gam (σ : L →+* L) (ϖ : L) {r : ℕ} (e : Fin r → ℕ) : AddSubgroup (Matrix (Fin r) (Fin r) L) where
  carrier := {Γ | (∀ k j, σ (Γ k j) = - Γ j k) ∧ ∀ k j, Valued.v (Γ k j) ≤ Valued.v ϖ ^ max (e k) (e j)}
  zero_mem' := ⟨fun k j => by simp, fun k j => by simp⟩
  add_mem' := by
    intro a b ha hb
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.add_apply, map_add (f := _), ha.1 k j, hb.1 k j]; ring
    · exact (Valuation.map_add _ _ _).trans (max_le (ha.2 k j) (hb.2 k j))
  neg_mem' := by
    intro a ha
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.neg_apply, map_neg, ha.1 k j]
    · simpa only [Matrix.neg_apply, Valuation.map_neg] using ha.2 k j

def gam0 (σ : L →+* L) (ϖ : L) {r : ℕ} (e : Fin r → ℕ) : AddSubgroup (Matrix (Fin r) (Fin r) L) where
  carrier := {Γ | (∀ k j, σ (Γ k j) = - Γ j k) ∧ ∀ k j, Valued.v (Γ k j) ≤ Valued.v ϖ ^ (e k + e j)}
  zero_mem' := ⟨fun k j => by simp, fun k j => by simp⟩
  add_mem' := by
    intro a b ha hb
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.add_apply, map_add (f := _), ha.1 k j, hb.1 k j]; ring
    · exact (Valuation.map_add _ _ _).trans (max_le (ha.2 k j) (hb.2 k j))
  neg_mem' := by
    intro a ha
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.neg_apply, map_neg, ha.1 k j]
    · simpa only [Matrix.neg_apply, Valuation.map_neg] using ha.2 k j

end GlobalTheory.Hk3.GramSep

end
