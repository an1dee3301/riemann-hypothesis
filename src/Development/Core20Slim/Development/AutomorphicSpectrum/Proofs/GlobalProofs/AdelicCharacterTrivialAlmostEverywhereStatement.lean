module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterTrivialAlmostEverywhere
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_haar_finite_infinite_product : ∀ (F : Type) [Field F] [NumberField F] (db : Measure (AF F)), IsCovolOne db → ∀ laminf : Measure (Ainf F), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → ∃ lf : Measure (Af F), lf.IsAddHaarMeasure ∧ lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 ∧ ∃ e : (Ainf F × Af F) ≃ᵐ AF F, (∀ p, e p = pairA F p.1 p.2) ∧ MeasurePreserving e (laminf.prod lf) db := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.ProdM.prodM | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.ProdM.prodM | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.ProdM.prodM <;> assumption)
