module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalProductActsOfAdelicProductActsFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localProduct_acts_of_adelicProduct_acts_first : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ κ' : Type) [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (Td : ((κ ⊕ κ' → AF F) → ℂ) → (κ ⊕ κ' → AF F) → ℂ),
    (∀ Φ₁ ∈ schA F κ, ∀ Φ₂ ∈ schA F κ', Td (boxFun Φ₁ Φ₂) = boxFun (T Φ₁) Φ₂) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), ∀ (φ₁' : (κ → Fv F v) → ℂ) (Φ' : (κ ⊕ κ' → Fv F v) → ℂ),
      Acts (evFin F v) T φ₁ φ₁' → Acts (evFin F v) Td (boxFun φ₁ φ₂) Φ' → Φ' = boxFun φ₁' φ₂ := by
  first | exact @GlobalTheory.BoxAct.boxFun_acts | exact GlobalTheory.BoxAct.boxFun_acts | (intros; apply GlobalTheory.BoxAct.boxFun_acts <;> assumption)
