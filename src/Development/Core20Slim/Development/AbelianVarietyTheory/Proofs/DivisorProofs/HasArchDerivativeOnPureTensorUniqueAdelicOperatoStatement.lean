module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchDerivativeOnPureTensorUniqueAdelicOperato
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPairApply
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasArchDerivativeOnPureTensor_unique_adelicOperators : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    {f f₁ f₂ : SInf F κ}, SD T f f₁ → SD T f f₂ → f₁ = f₂ := by
  first | exact @GlobalTheory.SDUnique.sd_unique | exact GlobalTheory.SDUnique.sd_unique | (intros; apply GlobalTheory.SDUnique.sd_unique <;> assumption)
