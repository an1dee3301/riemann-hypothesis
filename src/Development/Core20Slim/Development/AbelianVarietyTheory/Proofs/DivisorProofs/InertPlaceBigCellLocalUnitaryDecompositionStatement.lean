module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBigCellLocalUnitaryDecomposition
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InLat2
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_bigCell_local_unitary_decomposition : (∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det) →
  ∀ {K : Type} [Field K] (O : ValuationSubring K) (c : K →+* K), (∀ x, c (c x) = x) → (∀ x ∈ O, c x ∈ O) → (2 : K)⁻¹ ∈ O → (2 : K) ≠ 0 →
  ∀ {d : ℕ} (J : Matrix (Fin d) (Fin d) K), Jᵀ = -J.map c →
  ∀ (b : GL (Fin d) K) (δ : K), c δ = δ →
  (∀ i j, (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)) i j ∈ O) →
  (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)).det ≠ 0 →
  (δ • ((b : Matrix (Fin d) (Fin d) K)ᵀ * J * (b : Matrix (Fin d) (Fin d) K).map c)).det⁻¹ ∈ O →
  ∀ M M' : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K, M * M' = 1 → Mᵀ * dbl J * M.map c = dbl J →
  (∀ z, GlobalTheory.InertBigCell.InLat2 O b z → GlobalTheory.InertBigCell.InLat2 O b (M *ᵥ z) ∧ GlobalTheory.InertBigCell.InLat2 O b (M' *ᵥ z)) →
  ∃ P P' : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K, P * P' = 1 ∧ Pᵀ * dbl J * P.map c = dbl J ∧
    P * diagCols (Fin d) = diagCols (Fin d) ∧
    (∀ z, GlobalTheory.InertBigCell.InLat2 O b z → GlobalTheory.InertBigCell.InLat2 O b (P *ᵥ z) ∧ GlobalTheory.InertBigCell.InLat2 O b (P' *ᵥ z)) ∧
    ∃ N : Matrix (Fin d) (Fin d) K,
      N * ((2 : K)⁻¹ • ((P * M).toBlocks₁₁ + (P * M).toBlocks₁₂ + (P * M).toBlocks₂₁ + (P * M).toBlocks₂₂)) = 1 ∧
      ∀ u, GlobalTheory.InertBigCell.InLat O b u → GlobalTheory.InertBigCell.InLat O b (N *ᵥ u) := by
  first | exact @GlobalTheory.InertCellLocal.bigCell_local_step | exact GlobalTheory.InertCellLocal.bigCell_local_step | (intros; apply GlobalTheory.InertCellLocal.bigCell_local_step <;> assumption)
