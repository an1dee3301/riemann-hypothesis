module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumLatticeStabilizerBigCellFactorizati
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuumLatticeStabilizer_bigCell_factorization : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
    IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols d).det →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v,
      ((GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols d)⁻¹ *ᵥ z ∈
        GlobalTheory.InertSph.latAt W v) →
    ∃ p q : GlobalTheory.DblVac.UD σ W, p ∈ GlobalTheory.DblVac.KD σ W v ∧ p ∈ GlobalTheory.DblVac.PDiag σ W ∧
      q ∈ GlobalTheory.DblVac.KD σ W v ∧ q ∈ GlobalTheory.DblVac.PAnti σ W ∧ g = p * q := by
  first | exact @GlobalTheory.DblVacFactor.factor | exact GlobalTheory.DblVacFactor.factor | (intros; apply GlobalTheory.DblVacFactor.factor <;> assumption)
