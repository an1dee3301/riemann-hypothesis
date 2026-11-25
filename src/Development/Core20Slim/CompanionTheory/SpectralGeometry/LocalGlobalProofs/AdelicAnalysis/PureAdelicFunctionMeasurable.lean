module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalDensityOfSelfDualLatticeLemmas
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjections
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.Core20Slim.GroundTheory.GlobalFields.LocalAtPlace
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PureMeas

theorem borelSpace_ainf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) :
    BorelSpace (Fin n → Fin M → Ainf F ⊗[F] E) := by
  obtain ⟨⟨-, scA, -⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have scA' : SecondCountableTopology (Ainf F × Af F) := scA
  haveI : SecondCountableTopology (Ainf F) :=
    (isEmbedding_prodMkLeft (0 : Af F)).secondCountableTopology
  haveI : T2Space (Ainf F) := GlobalTheory.CompanionTheory.AdeleTop.t2Space_infiniteAdeleRing_of_numberField_field F
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)).2.2.2.2.2.2.2.1 n M

theorem borelSpace_af (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) :
    BorelSpace (Fin n → Fin M → AF F ⊗[F] E) := by
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := lcA
  haveI := scA
  haveI := t2A
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (AF F)).2.2.2.2.2.2.2.1 n M

theorem borelSpace_fv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := by
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : LocallyCompactSpace (Fv F v) := inferInstance
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  haveI : T2Space (Fv F v) := inferInstance
  exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)).2.2.2.2.2.2.2.1 n M

theorem measurable_pureL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → Measurable (pureL b S φinf φ) := by
  intro F E _ _ _ _ _ σ hσ d b n M S φinf φ hφinf hφ
  obtain ⟨hpi, hpf, hpv, -, hint, -⟩ := GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hσ d b n M
  haveI := borelSpace_af F E σ hσ n M
  haveI := borelSpace_ainf F E σ hσ n M
  haveI : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v => borelSpace_fv F E σ hσ n M v
  refine Measurable.indicator ?_ (hint S).measurableSet
  refine (hφinf.comp hpi.measurable).mul ?_
  refine Finset.measurable_prod _ fun v _ => ?_
  exact (hφ v).comp ((hpv v).comp hpf).measurable

end GlobalTheory.CompanionTheory.SW.PureMeas
