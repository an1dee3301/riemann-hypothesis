module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
public import Formalism.SatakeDualWeyl.StatementF
public import Init.ByCases
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Matrix

namespace GlobalTheory.Hk3.GramSep

theorem int_of_psi_trace_gam : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ),
  Formalism.UG.IsUnramInv ϖ σ q → (Valued.v δ = 1 ∧ σ δ = -δ) →
  (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) →
  ∀ (r : ℕ) (e : Fin r → ℕ) (Δ : Matrix (Fin r) (Fin r) L), (∀ j k, σ (Δ j k) = Δ k j) →
  (∀ Γ ∈ GlobalTheory.Hk3.GramSep.gam σ ϖ e, ψ (δ * Matrix.trace (Γ * Δ)) = 1) →
  ∀ j k, Δ j k * ϖ ^ max (e j) (e k) ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ q δ ψ hU hδ hne r e Δ hΔ hψ j k
  have hσ := hU.1
  have hv := hU.2.1
  have hw : δ * (Δ j k * ϖ ^ max (e j) (e k)) ∈ Formalism.UG.intL L := by
    refine GlobalTheory.Hk3.int_of_psi hU ψ hne _ (fun b hb => ?_)
    set c : L := b * ϖ ^ max (e j) (e k) with hc
    have hcv : Valued.v c ≤ Valued.v ϖ ^ max (e j) (e k) := by
      rw [hc, map_mul, map_pow]
      exact mul_le_of_le_one_left' hb
    have hmem : Matrix.single k j c + Matrix.single j k (-σ c) ∈ gam σ ϖ e := by
      refine ⟨fun a a' => ?_, fun a a' => ?_⟩
      · simp only [Matrix.add_apply, Matrix.single_apply, map_add (f := _), apply_ite σ, map_neg, hσ, map_zero,
          and_comm (a := k = a'), and_comm (a := j = a')]
        split_ifs <;> ring
      · rw [Matrix.add_apply]
        refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
        · rw [Matrix.single_apply]
          split_ifs with h
          · obtain ⟨rfl, rfl⟩ := h
            rw [max_comm]; exact hcv
          · simp
        · rw [Matrix.single_apply]
          split_ifs with h
          · obtain ⟨rfl, rfl⟩ := h
            rw [Valuation.map_neg, hv]; exact hcv
          · simp
    have h := hψ _ hmem
    have e1 : b * (δ * (Δ j k * ϖ ^ max (e j) (e k))) = δ * (c * Δ j k) := by rw [hc]; ring
    rw [e1, map_mul, map_mul σ c, hδ.2, hΔ, ← h]
    congr 1
    rw [Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul]
    simp only [smul_eq_mul]
    ring
  rw [GlobalTheory.Hk3.mem_intL_iff, map_mul, hδ.1, one_mul] at hw
  exact hw

end GlobalTheory.Hk3.GramSep
