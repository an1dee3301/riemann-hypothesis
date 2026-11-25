module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemAnnihilatorSmallBallEventually
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_annihilator_box_product : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v, v ∉ S → annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) = (v.adicCompletionIntegers F : Set (Fv F v))) → ∀ U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v), (∀ v, (0 : Fv F v) ∈ U v) → annF ψ (Coef.boxA S U) = Coef.boxA S (fun v => annV ψ v (U v)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA <;> assumption)
