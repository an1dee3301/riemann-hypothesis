module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlices
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponents
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductIntegralPureTensorEqProd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFCA
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix GlobalTheory.VacAny ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.WeilAdm.HaarSplit

theorem lintegral_split_mul : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)] [BorelSpace (κ → mixedEmbedding.mixedSpace F)]
    [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)]
    (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure] (μi : Measure (κ → mixedEmbedding.mixedSpace F)) [μi.IsAddHaarMeasure]
    (μf : Measure (κ → Af F)) [μf.IsAddHaarMeasure],
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ (fi : (κ → mixedEmbedding.mixedSpace F) → ℝ≥0∞) (g : (κ → Af F) → ℝ≥0∞),
      Measurable fi → Measurable g →
        ∫⁻ x, fi (fun i => evI F (x i)) * g (fun i => sndA F (x i)) ∂μ = c * ((∫⁻ z, fi z ∂μi) * ∫⁻ y, g y ∂μf) := by
  intro F _ _ κ _ mA _ mI _ mf _ μ _ μi _ μf _
  haveI : LocallyCompactSpace (Af F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI : BorelSpace ((κ → mixedEmbedding.mixedSpace F) × (κ → Af F)) := Prod.borelSpace
  haveI : (μi.prod μf).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μi μf
  have hH : ((μ.map (splitE F κ).symm)).IsAddHaarMeasure :=
    (splitE F κ).symm.isAddHaarMeasure_map μ (continuous_splitE_symm F κ) (continuous_splitE F κ)
  let em : (κ → AF F) ≃ᵐ ((κ → mixedEmbedding.mixedSpace F) × (κ → Af F)) :=
    (Homeomorph.mk (splitE F κ).symm.toEquiv (continuous_splitE_symm F κ) (continuous_splitE F κ)).toMeasurableEquiv
  set c : NNReal := Measure.addHaarScalarFactor (μ.map (splitE F κ).symm) (μi.prod μf) with hc
  have heq : μ.map (splitE F κ).symm = c • (μi.prod μf) :=
    Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨(c : ℝ≥0∞), ?_, ENNReal.coe_ne_top, ?_⟩
  · exact ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  intro fi g hfi hg
  have h1 : ∫⁻ x, fi (fun i => evI F (x i)) * g (fun i => sndA F (x i)) ∂μ
      = ∫⁻ p, fi p.1 * g p.2 ∂(μ.map (splitE F κ).symm) := by
    rw [show μ.map (splitE F κ).symm = μ.map em from rfl, lintegral_map_equiv]
    rfl
  rw [h1, heq, lintegral_smul_measure, lintegral_prod_mul hfi.aemeasurable hg.aemeasurable]
  rfl

end GlobalTheory.WeilAdm.HaarSplit
