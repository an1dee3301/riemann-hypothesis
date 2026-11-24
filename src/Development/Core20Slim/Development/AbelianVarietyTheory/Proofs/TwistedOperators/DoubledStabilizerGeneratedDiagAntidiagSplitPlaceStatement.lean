module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledStabilizerGeneratedDiagAntidiagSplitPlace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledStabilizer_generated_diag_antidiag_splitPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → PsiUnr B.ψ v →
    (2 : 𝓞 F) ∉ v.asIdeal → 3 < Ideal.absNorm v.asIdeal → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ G.W),
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PAnti σ G.W → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, g ∈ H := by
  first | exact @GlobalTheory.DblVac.gen_diag_anti_split | exact GlobalTheory.DblVac.gen_diag_anti_split | (intros; apply GlobalTheory.DblVac.gen_diag_anti_split <;> assumption)
