module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
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

noncomputable section

namespace GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem hform_smul_smul (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (s t : L) (u v : Fin n → L) :
    Formalism.UG.hform σ J (s • u) (t • v) = σ s * t * Formalism.UG.hform σ J u v := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mulVec_single_int {n : ℕ} (V : Matrix (Fin n) (Fin n) L) (hV : ∀ i j, V i j ∈ Formalism.UG.intL L) (i : Fin n) :
    ∀ r, (V *ᵥ Pi.single i (1 : L)) r ∈ Formalism.UG.intL L := by
  intro r
  have : (V *ᵥ Pi.single i (1 : L)) r = V r i := by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [this]; exact hV r i

theorem single_eq_smul {n : ℕ} (i : Fin n) (c : L) : (Pi.single i c : Fin n → L) = c • Pi.single i (1 : L) := by
  ext r; by_cases h : r = i
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem gram_class_columns : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L)
    (V : Matrix (Fin n) (Fin n) L) (a : Fin n → ℕ), (∀ i j, V i j ∈ Formalism.UG.intL L) →
    (∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (x *ᵥ (V *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j))) →
    GlobalTheory.Hk3.HoweG.GramEq σ JT x y →
    ∀ i j : Fin n, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (min (a i) (a j))
      (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (y *ᵥ (V *ᵥ Pi.single i (ϖ ^ a i))) (y *ᵥ (V *ᵥ Pi.single j (ϖ ^ a j))) -
        Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (x *ᵥ (V *ᵥ Pi.single i (ϖ ^ a i))) (x *ᵥ (V *ᵥ Pi.single j (ϖ ^ a j)))) := by
  intro L _ _ ϖ σ q hU n n' JT x y V a hV hiff hG i j
  have hϖv : Valued.v ϖ ≤ 1 := by
    rw [hU.2.2.2.1]; exact le_of_lt (by decide)
  have hϖ : ϖ ∈ Formalism.UG.intL L := hϖv
  set k := max (a i) (a j) with hk
  set c : L := ϖ ^ k with hc
  have hcI : c ∈ Formalism.UG.intL L := (Formalism.UG.intL L).pow_mem hϖ _

  have hcond : ∀ l, a l ≤ k → ∀ r, (x *ᵥ (c • (V *ᵥ Pi.single l (1 : L)))) r ∈ Formalism.UG.intL L := by
    intro l hl
    have hI : ∀ t, (Pi.single l c : Fin n → L) t ∈ Formalism.UG.intL L := by
      intro t; by_cases h : t = l
      · subst h; simpa using hcI
      · simp [Pi.single_apply, h, (Formalism.UG.intL L).zero_mem]
    have := (hiff (Pi.single l c) hI).mpr (by
      intro t; by_cases h : t = l
      · subst h
        refine ⟨ϖ ^ (k - a t), (Formalism.UG.intL L).pow_mem hϖ _, ?_⟩
        simp [hc, ← pow_add, Nat.add_sub_cancel' hl]
      · simpa [Pi.single_apply, h] using dvdPow_zero ϖ (a t))
    rwa [single_eq_smul, mulVec_smul] at this
  have hD := hG _ _ (mulVec_single_int V hV i) (mulVec_single_int V hV j) c hcI
    (hcond i (le_max_left _ _)) (hcond j (le_max_right _ _))
  refine ⟨_, hD, ?_⟩
  rw [single_eq_smul i, single_eq_smul j, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul, mulVec_smul,
    hform_smul_smul, hform_smul_smul, map_pow, hU.2.2.1, hc, ← mul_sub, ← mul_assoc, ← pow_add, ← pow_add,
    min_add_max]

end GlobalTheory.Hk3.IntWitt

end
