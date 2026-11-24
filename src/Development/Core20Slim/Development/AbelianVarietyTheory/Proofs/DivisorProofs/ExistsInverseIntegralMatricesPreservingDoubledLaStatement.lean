module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseIntegralMatricesPreservingDoubledLa
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverse_integral_matrices_preserving_doubled_lattice : ∀ (A O : Type) [CommRing A] [CommRing O] (ι : O →ₙ+* A) (n : ℕ) (P Q : Matrix (Fin n) (Fin n) A)
    (Λ : Set (Fin n → A)), Function.Injective ι → P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) A) →
    Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) A) → ι 1 • P = P → ι 1 • Q = Q →
    (∀ z, z ∈ Λ ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i)) →
    ∀ M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A, M * M' = 1 →
    (∀ z : Fin n ⊕ Fin n → A, z ∘ Sum.inl ∈ Λ → z ∘ Sum.inr ∈ Λ →
      (M *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M *ᵥ z) ∘ Sum.inr ∈ Λ ∧ (M' *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M' *ᵥ z) ∘ Sum.inr ∈ Λ) →
    ∃ G G' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, G * G' = 1 ∧
      M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι := by
  first | exact @GlobalTheory.LatticeStab.matrix_in_diag_basis | exact GlobalTheory.LatticeStab.matrix_in_diag_basis | (intros; apply GlobalTheory.LatticeStab.matrix_in_diag_basis <;> assumption)
