module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Quot
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
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

open Matrix

namespace GlobalTheory.Hk3.GramSep

theorem gam_quot_finite : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧ ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K) →
  ∀ (r : ℕ) (e : Fin r → ℕ), Finite (↥(GlobalTheory.Hk3.GramSep.gam σ ϖ e) ⧸
    (GlobalTheory.Hk3.GramSep.gam0 σ ϖ e).addSubgroupOf (GlobalTheory.Hk3.GramSep.gam σ ϖ e)) := by
  intro L _ _ ϖ σ hϖ hR r e
  classical
  have hle1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ]
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) ≤ 1)
  set K : ℕ := ∑ k, ∑ j, (e k + e j) with hK
  obtain ⟨R, -, hRc⟩ := hR K
  have hKge : ∀ k j, e k + e j ≤ K := by
    intro k j
    have h1 : e k + e j ≤ ∑ j', (e k + e j') :=
      Finset.single_le_sum (f := fun j' => e k + e j') (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 : ∑ j', (e k + e j') ≤ ∑ k', ∑ j', (e k' + e j') :=
      Finset.single_le_sum (f := fun k' => ∑ j', (e k' + e j')) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    exact h1.trans h2
  have hint : ∀ Γ : ↥(gam σ ϖ e), ∀ k j, (Γ : Matrix (Fin r) (Fin r) L) k j ∈ Formalism.UG.intL L := by
    intro Γ k j
    show Valued.v ((Γ : Matrix (Fin r) (Fin r) L) k j) ≤ 1
    exact (Γ.2.2 k j).trans (pow_le_one' hle1 _)
  have hch : ∀ Γ : ↥(gam σ ϖ e), ∀ k j, ∃ x ∈ R, Valued.v ((Γ : Matrix (Fin r) (Fin r) L) k j - x) ≤ Valued.v ϖ ^ K :=
    fun Γ k j => hRc _ (hint Γ k j)
  let g : ↥(gam σ ϖ e) → (Fin r → Fin r → ↥R) := fun Γ k j => ⟨(hch Γ k j).choose, (hch Γ k j).choose_spec.1⟩
  have hg : ∀ (Γ : ↥(gam σ ϖ e)) k j, Valued.v ((Γ : Matrix (Fin r) (Fin r) L) k j - (g Γ k j : L)) ≤ Valued.v ϖ ^ K :=
    fun Γ k j => (hch Γ k j).choose_spec.2
  let h : (↥(gam σ ϖ e) ⧸ (gam0 σ ϖ e).addSubgroupOf (gam σ ϖ e)) → (Fin r → Fin r → ↥R) :=
    fun q => g (Quotient.out q)
  have hinj : Function.Injective h := by
    intro q1 q2 hq
    rw [← QuotientAddGroup.out_eq' q1, ← QuotientAddGroup.out_eq' q2, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    set a := Quotient.out q1
    set b := Quotient.out q2
    have hab : g a = g b := hq
    have hmem : ((-a + b : ↥(gam σ ϖ e)) : Matrix (Fin r) (Fin r) L) ∈ gam σ ϖ e := (-a + b).2
    refine ⟨hmem.1, fun k j => ?_⟩
    have e1 : ((-a + b : ↥(gam σ ϖ e)) : Matrix (Fin r) (Fin r) L) k j
        = ((b : Matrix (Fin r) (Fin r) L) k j - (g b k j : L)) - ((a : Matrix (Fin r) (Fin r) L) k j - (g a k j : L)) := by
      rw [hab]; simp; ring
    rw [e1]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    · exact (hg b k j).trans (pow_le_pow_right_of_le_one' hle1 (hKge k j))
    · exact (hg a k j).trans (pow_le_pow_right_of_le_one' hle1 (hKge k j))
  exact Finite.of_injective h hinj

end GlobalTheory.Hk3.GramSep
