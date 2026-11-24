module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphDetLowerRowNeZeroField
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_graph_det_ne_zero : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → (∃ ε : k, ε ≠ 0 ∧ σ ε = -ε) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) k), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k, g.det ≠ 0 →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map σ = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) k, Zᵀ * J + J * Z.map σ = 0 ∧ (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det ≠ 0 := by
  first | exact @GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field | exact GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field | (intros; apply GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field <;> assumption)
