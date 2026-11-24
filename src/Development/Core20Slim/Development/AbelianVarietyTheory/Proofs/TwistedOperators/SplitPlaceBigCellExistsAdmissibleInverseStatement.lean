module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceBigCellExistsAdmissibleInverse
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
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
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_bigCell_exists_admissible_inverse_alt : (∀ {R : Type} [CommRing R] [IsLocalRing R], IsUnit (2 : R) → ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) R), IsUnit S.det →
    ∀ (G₁ G₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R), IsUnit G₁.det →
      G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) →
      ∃ X₁ X₂ : Matrix (Fin n) (Fin n) R, X₁ᵀ * S + S * X₂ = 0 ∧
        IsUnit (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ + G₁.toBlocks₂₁ + G₁.toBlocks₂₂ +
          X₁ * (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ - G₁.toBlocks₂₁ - G₁.toBlocks₂₂)).det ∧
        IsUnit (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ + G₂.toBlocks₂₁ + G₂.toBlocks₂₂ +
          X₂ * (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ - G₂.toBlocks₂₁ - G₂.toBlocks₂₂)).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), (∀ i j, σ (W.J j i) = -W.J i j) →
    IsUnit (2 : v.adicCompletionIntegers F) →
    ∀ (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) →
      (∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) →
      ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
        Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.SplitPlaceBigCell.splitPlace_bigCell_exists_admissible_inverse | exact GlobalTheory.SplitPlaceBigCell.splitPlace_bigCell_exists_admissible_inverse | (intros; apply GlobalTheory.SplitPlaceBigCell.splitPlace_bigCell_exists_admissible_inverse <;> assumption)
