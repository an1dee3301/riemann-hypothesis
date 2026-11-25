module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.MeasurableSetUH
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinUnfoldingIdentity
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.MeasurableSetIntF
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Classical
public import Init.Core
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.List
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_UH (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (bs : Module.Basis (Fin d) F E) (n : ℕ)
    (ν : Measure (HermR (AF F) σ n)) (f : HermR (AF F) σ n → ℂ) (hf : Integrable f ν) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => ∫ b in UH σ bs n S, f b ∂ν) atTop (nhds (∫ b, f b ∂ν)) := by
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  have he : ∀ S, ∫ b in UH σ bs n S, f b ∂ν = ∫ b, (UH σ bs n S).indicator f b ∂ν := fun S =>
    (integral_indicator (measurableSet_UH σ hCM bs n S)).symm
  simp_rw [he]
  refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖f y‖) ?_ ?_ hf.norm ?_
  · exact Filter.Eventually.of_forall fun S => hf.aestronglyMeasurable.indicator (measurableSet_UH σ hCM bs n S)
  · refine Filter.Eventually.of_forall fun S => Filter.Eventually.of_forall fun y => ?_
    by_cases h : y ∈ UH σ bs n S
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  · refine Filter.Eventually.of_forall fun y => ?_
    have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ hermV σ v (hermFin σ y) ∈ latH σ bs v n}.Finite :=
      Filter.eventually_cofinite.1 (GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.ev_latH σ bs y)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop hfin.toFinset] with S hS
    have hmem : y ∈ UH σ bs n S := by
      intro v hv
      by_contra hcon
      exact hv (hS (hfin.mem_toFinset.2 hcon))
    simp [Set.indicator_of_mem hmem]

end PositivityTheory.SiegelWeilFormula.GFac

end
