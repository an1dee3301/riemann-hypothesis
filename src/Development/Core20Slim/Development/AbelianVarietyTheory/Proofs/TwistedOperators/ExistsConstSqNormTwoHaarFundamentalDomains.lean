module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PhaseApply
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.NormRed

theorem sq_norm_two_haar : ∀ (D : D7) (V' W : HSp D) (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ (μ'' : Measure (WO V' W)) (𝓕'' : Set (WO V' W)), IsCovolOne (ratL W V') μ'' 𝓕'' → ∃ c : ENNReal, ∀ g : WO V' W → ℂ, Continuous g → (∀ γ ∈ ratL W V', ∀ w, ‖g (γ + w)‖ = ‖g w‖) → ∫⁻ x in 𝓕', ‖g x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x in 𝓕'', ‖g x‖ₑ ^ 2 ∂μ'' := by
  intro D V' W μ' 𝓕' hμ' hF' μ'' 𝓕'' h''
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (WO V' W) := i1
  haveI : LocallyCompactSpace (WO V' W) := i2
  haveI : SecondCountableTopology (WO V' W) := i3
  haveI : T2Space (WO V' W) := i4
  haveI : DiscreteTopology (ratL W V') := i5
  haveI : TopologicalSpace.SeparableSpace (ratL W V') := inferInstance
  haveI : Countable (ratL W V') := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : MeasurableConstVAdd (ratL W V') (WO V' W) :=
    ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  obtain ⟨hμ'', hF'', -⟩ := h''
  haveI : VAddInvariantMeasure (ratL W V') (WO V' W) μ'' :=
    ⟨fun c s _ => measure_preimage_add μ'' (c : WO V' W) s⟩
  have e := Measure.isAddLeftInvariant_eq_smul μ' μ''
  set c := Measure.addHaarScalarFactor μ' μ''
  have hc : c ≠ 0 := (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' μ'').ne'
  have hac : μ'' ≪ μ' := by
    rw [e]; exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc)
  have hF2 : IsAddFundamentalDomain (ratL W V') 𝓕' μ'' := hF'.mono hac
  refine ⟨(c : ENNReal), fun g hg hper => ?_⟩
  have hp : ∀ (γ : ratL W V') (x : WO V' W), ‖g (γ +ᵥ x)‖ₑ ^ 2 = ‖g x‖ₑ ^ 2 := by
    intro γ x
    rw [AddSubgroup.vadd_def, vadd_eq_add]
    have h1 : ‖g ((γ : WO V' W) + x)‖₊ = ‖g x‖₊ := NNReal.eq (hper γ γ.2 x)
    simp only [enorm_eq_nnnorm, h1]
  rw [e, Measure.restrict_smul, lintegral_smul_measure, hF2.setLIntegral_eq hF'' _ hp]
  rfl

end GlobalTheory.Twist.NormRed
