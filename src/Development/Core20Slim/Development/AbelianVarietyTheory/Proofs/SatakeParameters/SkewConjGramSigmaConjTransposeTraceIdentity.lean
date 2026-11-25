module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
public import Formalism.SatakeDualWeyl.Statement
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Matrix

namespace GlobalTheory

theorem skewConj_cT_mul_and_trace :
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L), (∀ x, σ (σ x) = x) →
  ∀ (n r : ℕ) (JS : GL (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) → (∀ k j, σ (Γ k j) = - Γ j k) →
  Formalism.UG.cT σ (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L))) ∧
  ∀ (n' : ℕ) (JT : GL (Fin n') L) (y : Matrix (Fin n') (Fin n) L),
    Matrix.trace ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ y * (JT : Matrix (Fin n') (Fin n') L) * y) =
      Matrix.trace (Γ * (Formalism.UG.cT σ (y * M) * (JT : Matrix (Fin n') (Fin n') L) * (y * M))) := by
  intro L _ _ σ hσ n r JS M Γ hJ hΓ
  have hmul : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) L) (B : Matrix (Fin b) (Fin c) L),
      Formalism.UG.cT σ (A * B) = Formalism.UG.cT σ B * Formalism.UG.cT σ A := by
    intro a b c A B
    simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have hcc : Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
    ext i j
    simp [Formalism.UG.cT, hσ]
  have hJ' : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS := by
    ext i j
    simp [Formalism.UG.cT, hJ]
  have hΓ' : Formalism.UG.cT σ Γ = -Γ := by
    ext i j
    simp [Formalism.UG.cT, hΓ]
  refine ⟨?_, ?_⟩
  · rw [hmul, hmul, hmul, hcc, hJ', hΓ']
    simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
  · intro n' JT y
    rw [hmul, Matrix.mul_assoc (M * Γ * Formalism.UG.cT σ M), Units.mul_inv, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm M]
    simp only [Matrix.mul_assoc]

end GlobalTheory
