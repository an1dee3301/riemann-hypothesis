module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeToPlaceDenominatorUnramifiedTrace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdeleSupportedAtFinitePlaceOfSupportedAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_to_place_denominator_unramified_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (v : Pl (F := F)) (e : E),
    (∀ o : 𝓞 E, algebraMap F (Fv F v) (Algebra.trace F E ((o : E) * e)) ∈ v.adicCompletionIntegers F) →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ IsIntegral ℤ (algebraMap F E (t : F) * e) := by
  first | exact @GlobalTheory.UnramTraceDenom.exists_not_mem_mul_isIntegral | exact GlobalTheory.UnramTraceDenom.exists_not_mem_mul_isIntegral | (intros; apply GlobalTheory.UnramTraceDenom.exists_not_mem_mul_isIntegral <;> assumption)
