module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlices
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
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
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.WeilL2Isometry

open MeasureTheory GlobalTheory.WeilAdm.HaarSplit
open scoped ENNReal Classical

theorem l2A_eq_of_isUnitaryOn : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] {G : Type} [Group G]
    (om : G →* Module.End ℂ ((κ → AF F) → ℂ)), (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) → IsUnitaryOn (adeleClass F) om →
    ∃ μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
      ∀ p, ∀ Φ ∈ schA F κ, GlobalTheory.WeilL2Words.l2A F μ (om p Φ) = GlobalTheory.WeilL2Words.l2A F μ Φ := by
  intro F _ _ κ _ G _ om hpres hU
  haveI := volume_isAddHaar F κ
  haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI : SFinite ν := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  haveI hνH : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : ((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hμH : Measure.IsAddHaarMeasure (((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).map (splitE F κ)) :=
    (splitE F κ).isAddHaarMeasure_map _ (continuous_splitE F κ) (continuous_splitE_symm F κ)
  let em : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AdeleRing (𝓞 F) F) :=
    (Homeomorph.mk (splitE F κ).toEquiv (continuous_splitE F κ) (continuous_splitE_symm F κ)).toMeasurableEquiv
  have hint : ∀ h : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞,
      ∫⁻ x, h x ∂(((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).map (splitE F κ)) = ∫⁻ p, h (splitE F κ p) ∂((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν) :=
    fun h => lintegral_map_equiv h em
  have key : ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilL2Words.l2A F ν Ψ = ∫⁻ x, ‖Ψ x‖ₑ ^ 2 ∂(((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).map (splitE F κ)) := by
    intro Ψ hΨ
    rw [hint]
    have hHm : Measurable fun p => ‖Ψ (splitE F κ p)‖ₑ ^ 2 :=
      (continuous_comp_splitE F κ Ψ hΨ).measurable.enorm.pow_const 2
    rw [lintegral_prod_symm _ hHm.aemeasurable]
    rfl
  refine ⟨ν, hνH, fun p Φ hΦ => ?_⟩
  rw [key _ (hpres p Φ hΦ), key _ hΦ]
  exact hU _ hμH p Φ hΦ

end GlobalTheory.WeilL2Isometry
