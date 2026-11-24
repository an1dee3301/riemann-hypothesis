module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleUnipotentSplitPlaceHermitian
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
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
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
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
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_unipotent_at_split_place : (∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ V v,
      ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt V v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt V v) ∧
        Yᵀ * incM F V.J + incM F V.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt V v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt V v := by
  first | exact @GlobalTheory.SplitChooseHerm.exists_admissible_unipotent_split_place_hermitian | exact GlobalTheory.SplitChooseHerm.exists_admissible_unipotent_split_place_hermitian | (intros; apply GlobalTheory.SplitChooseHerm.exists_admissible_unipotent_split_place_hermitian <;> assumption)
