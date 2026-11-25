module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrArchPairAdeleJoin
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.LiminfLimsup
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Instances.Nat
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section
open MeasureTheory Filter Topology

namespace GlobalTheory.WeilL2Words

theorem l2A_eq_zero_of_tendsto (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _))
    (D : (κ → AdeleRing (𝓞 F) F) → ℂ) (G : ℕ → (κ → AdeleRing (𝓞 F) F) → ℂ) (hG : ∀ n, G n ∈ GlobalTheory.WeilM.schA F κ)
    (hD : ∀ a, Filter.Tendsto (fun n => G n a) Filter.atTop (nhds (D a)))
    (h0 : Filter.Tendsto (fun n => GlobalTheory.WeilL2Words.l2A F μ (G n)) Filter.atTop (nhds 0)) : GlobalTheory.WeilL2Words.l2A F μ D = 0 := by
  letI : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := Pi.opensMeasurableSpace
  have hc : Continuous fun z : ℂ => ‖z‖ₑ ^ 2 := (ENNReal.continuous_pow 2).comp continuous_enorm
  have hin : ∀ y, (∫⁻ x, ‖D (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) ≤
      liminf (fun n => ∫⁻ x, ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) atTop := by
    intro y
    have hm : ∀ n, AEMeasurable (fun x => ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) volume := by
      intro n
      obtain ⟨s, hs⟩ := GlobalTheory.WeilCont.exists_slice F (hG n) y
      have e : (fun x => ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) = fun x => ‖s x‖ₑ ^ 2 := by
        funext x; rw [hs]
      rw [e]
      exact (hc.comp s.continuous).measurable.aemeasurable
    calc (∫⁻ x, ‖D (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2)
        = ∫⁻ x, liminf (fun n => ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) atTop := by
          refine lintegral_congr fun x => ?_
          exact (((hc.tendsto _).comp (hD _)).liminf_eq).symm
      _ ≤ _ := lintegral_liminf_le' hm
  have hmeas : ∀ n, AEMeasurable (fun y => ∫⁻ x, ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) μ := by
    intro n
    obtain ⟨m, f, g, hg, he⟩ := schA_exists_sum F (hG n)
    have hlc : IsLocallyConstant (fun y => ∫⁻ x, ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro y
      have hev : ∀ᶠ z in 𝓝 y, ∀ i, g i z = g i y :=
        Filter.eventually_all.2 fun i => (hg i).1.eventually_eq y
      filter_upwards [hev] with z hz
      refine lintegral_congr fun x => ?_
      simp only [he, Finset.sum_apply, GlobalTheory.WeilCont.pureA_adeleJoin, hz]
    exact hlc.continuous.measurable.aemeasurable
  refine le_antisymm ?_ (bot_le)
  calc l2A F μ D = ∫⁻ y, (∫⁻ x, ‖D (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) ∂μ := rfl
    _ ≤ ∫⁻ y, liminf (fun n => ∫⁻ x, ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) atTop ∂μ := lintegral_mono hin
    _ ≤ liminf (fun n => ∫⁻ y, (∫⁻ x, ‖G n (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) ∂μ) atTop := lintegral_liminf_le' hmeas
    _ = 0 := h0.liminf_eq

end GlobalTheory.WeilL2Words

end
