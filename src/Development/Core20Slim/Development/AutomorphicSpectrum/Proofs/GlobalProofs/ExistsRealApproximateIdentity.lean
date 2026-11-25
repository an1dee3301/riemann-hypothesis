module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

theorem integrable_inf_mul_indicator_finiteMass : ∀ (F : Type) [Field F] [NumberField F] (db : Measure (AF F)) (laminf : Measure (Ainf F)) (lf : Measure (Af F)), laminf.IsAddHaarMeasure → lf.IsAddHaarMeasure → ∀ e : (Ainf F × Af F) ≃ᵐ AF F, (∀ p, e p = pairA F p.1 p.2) → MeasurePreserving e (laminf.prod lf) db → ∀ (g : Ainf F → ℂ) (B : Set (Af F)), Integrable g laminf → MeasurableSet B → lf B ≠ ⊤ → Integrable (fun y => g (fstA F y) * B.indicator (fun _ => (1 : ℂ)) (sndA F y)) db := by
  intro F _ _ db laminf lf _ _ e he hmp g B hg hB hfin
  have hind : Integrable (B.indicator (fun _ => (1 : ℂ))) lf :=
    (integrable_indicator_iff hB).mpr (integrableOn_const hfin)
  refine (hmp.integrable_comp_emb e.measurableEmbedding).mp ?_
  have hfun : ((fun y => g (fstA F y) * B.indicator (fun _ => (1 : ℂ)) (sndA F y)) ∘ e) =
      fun p : Ainf F × Af F => g p.1 * B.indicator (fun _ => (1 : ℂ)) p.2 := by
    funext p
    simp only [Function.comp_apply, he p]
    rfl
  rw [hfun]
  exact hg.mul_prod hind

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
