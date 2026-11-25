module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
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
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Matrix

namespace GlobalTheory.Hk3.GramSep

theorem trace_skewHermitian_gram_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (δ : L), (∀ x, Valued.v (σ x) = Valued.v x) → δ ∈ Formalism.UG.intL L →
  ∀ (n n' r : ℕ) (JT : GL (Fin n') L) (a : GL (Fin n) L) (y : Matrix (Fin n') (Fin n) L)
    (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) → (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → Γ ∈ GlobalTheory.Hk3.GramSep.gam0 σ ϖ e →
  δ * Matrix.trace (Γ * (Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M))) ∈ Formalism.UG.intL L := by
  intro L _ _ ϖ σ δ hv hδ n n' r JT a y M e Γ hJT hya haM hΓ
  have hmem : ∀ x : L, x ∈ Formalism.UG.intL L ↔ Valued.v x ≤ 1 := fun _ => Iff.rfl
  set N := y * M with hNdef
  have hNe : N = (y * (a : Matrix (Fin n) (Fin n) L)) * (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) := by
    rw [hNdef, Matrix.mul_assoc, ← Matrix.mul_assoc (a : Matrix (Fin n) (Fin n) L)]
    have : (a : Matrix (Fin n) (Fin n) L) * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [this, Matrix.one_mul]
  have hN : ∀ q k, N q k * ϖ ^ e k ∈ Formalism.UG.intL L := by
    intro q k
    rw [hNe, Matrix.mul_apply, Finset.sum_mul]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [mul_assoc]
    exact Subring.mul_mem _ (hya q i) (haM i k)
  have hNσ : ∀ p j, σ (N p j) * ϖ ^ e j ∈ Formalism.UG.intL L := by
    intro p j
    have h := hN p j
    rw [hmem] at h ⊢
    rw [map_mul, hv]; rw [map_mul] at h; exact h
  have hG : ∀ j k, (Formalism.UG.cT σ N * (JT : Matrix (Fin n') (Fin n') L) * N) j k * ϖ ^ (e j + e k) ∈ Formalism.UG.intL L := by
    intro j k
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Subring.sum_mem _ fun q _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
    refine Subring.sum_mem _ fun p _ => ?_
    have hc : Formalism.UG.cT σ N j p = σ (N p j) := rfl
    rw [hc, pow_add]
    have : σ (N p j) * (JT : Matrix (Fin n') (Fin n') L) p q * N q k * (ϖ ^ e j * ϖ ^ e k) =
        (σ (N p j) * ϖ ^ e j) * (JT : Matrix (Fin n') (Fin n') L) p q * (N q k * ϖ ^ e k) := by ring
    rw [this]
    exact Subring.mul_mem _ (Subring.mul_mem _ (hNσ p j) (hJT p q)) (hN q k)
  refine Subring.mul_mem _ hδ ?_
  rw [Matrix.trace]
  refine Subring.sum_mem _ fun k _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [hmem, map_mul]
  have h1 := hΓ.2 k j
  have h2 := hG j k
  rw [hmem, map_mul, map_pow] at h2
  calc Valued.v (Γ k j) * Valued.v ((Formalism.UG.cT σ N * (JT : Matrix (Fin n') (Fin n') L) * N) j k)
      ≤ Valued.v ϖ ^ (e k + e j) * Valued.v ((Formalism.UG.cT σ N * (JT : Matrix (Fin n') (Fin n') L) * N) j k) :=
        mul_le_mul_of_nonneg_right h1 zero_le'
    _ = Valued.v ((Formalism.UG.cT σ N * (JT : Matrix (Fin n') (Fin n') L) * N) j k) * Valued.v ϖ ^ (e j + e k) := by
        rw [mul_comm, add_comm]
    _ ≤ 1 := h2

end GlobalTheory.Hk3.GramSep
