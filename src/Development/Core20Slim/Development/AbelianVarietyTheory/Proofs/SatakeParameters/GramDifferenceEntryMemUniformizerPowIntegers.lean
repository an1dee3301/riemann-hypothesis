module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem gram_entry_eq_hform {L : Type} [Field L] (σ : L →+* L) {n n' r : ℕ}
    (J : Matrix (Fin n') (Fin n') L) (z : Matrix (Fin n') (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (j k : Fin r) :
    (Formalism.UG.cT σ (z * M) * J * (z * M)) j k =
      Formalism.UG.hform σ J (z *ᵥ fun i => M i j) (z *ᵥ fun i => M i k) := by
  have hz : ∀ a l, (z * M) a l = (z *ᵥ fun i => M i l) a := fun a l => by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  simp only [Formalism.UG.cT, Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hz,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem gramDiff_entry_int : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (n n' r : ℕ) (JT : GL (Fin n') L) (a : GL (Fin n) L)
  (x y : Matrix (Fin n') (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
  ϖ ∈ Formalism.UG.intL L → (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
    ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔ ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) → (∀ i k, M i k ∈ Formalism.UG.intL L) → (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.GramEq σ JT x y →
  ∀ j k, ((Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M)) - (Formalism.UG.cT σ (x * M) * (JT : Matrix (Fin n') (Fin n') L) * (x * M))) j k * ϖ ^ max (e j) (e k) ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ n n' r JT a x y M e hϖ hiff hM haM hG j k
  have hcO : ∀ t : ℕ, ϖ ^ t ∈ Formalism.UG.intL L := fun t => Subring.pow_mem _ hϖ t
  have hx : ∀ l, e l ≤ max (e j) (e k) →
      ∀ i, (x *ᵥ ((ϖ ^ max (e j) (e k)) • fun i => M i l)) i ∈ Formalism.UG.intL L := by
    intro l hl
    refine (hiff ((ϖ ^ max (e j) (e k)) • fun i => M i l) (fun i => ?_)).1
      ⟨(ϖ ^ max (e j) (e k)) • (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ fun i => M i l),
        fun i => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; exact Subring.mul_mem _ (hcO _) (hM i l)
    · have h1 : ((ϖ ^ max (e j) (e k)) • (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ fun i => M i l)) i =
          ((((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i l * ϖ ^ e l) * ϖ ^ (max (e j) (e k) - e l) := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hl]
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm]
      rw [h1]; exact Subring.mul_mem _ (haM i l) (hcO _)
    · rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, a.mul_inv, Matrix.one_mulVec]
  have key := hG (fun i => M i j) (fun i => M i k) (fun i => hM i j) (fun i => hM i k) _ (hcO _)
    (hx j (le_max_left _ _)) (hx k (le_max_right _ _))
  rw [Matrix.sub_apply, gram_entry_eq_hform, gram_entry_eq_hform, mul_comm]
  exact key

end GlobalTheory.Hk3.HoweG
