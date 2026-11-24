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
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
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
open MeasureTheory
namespace GlobalTheory.WeilL2Words

theorem eq_zero_of_l2A_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ D ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.l2A F μ D = 0 → D = 0 := by
  intro F _ _ κ _ μ hμ D hD h0
  letI : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  funext a
  by_contra ha
  set x0 := archPart F a
  set y0 : κ → FiniteAdeleRing (𝓞 F) F := fun i => (a i).2
  have ha0 : D (GlobalTheory.WeilCont.adeleJoin F x0 y0) ≠ 0 := by
    rw [adeleJoin_archPart]; exact ha
  obtain ⟨n, f, g, hg, hDs⟩ := schA_exists_sum F hD
  obtain ⟨s, hs⟩ := GlobalTheory.WeilCont.exists_slice F hD y0
  set V : Set (κ → FiniteAdeleRing (𝓞 F) F) := {y | ∀ i, g i y = g i y0}
  have hVo : IsOpen V := by
    have : V = ⋂ i, {y | g i y = g i y0} := by ext y; simp [V]
    rw [this]
    exact isOpen_iInter_of_finite fun i => (hg i).1.isOpen_fiber _
  have hV : ∀ y ∈ V, ∀ x, D (GlobalTheory.WeilCont.adeleJoin F x y) = s x := by
    intro y hy x
    rw [hs, hDs, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GlobalTheory.WeilCont.pureA_adeleJoin, GlobalTheory.WeilCont.pureA_adeleJoin, hy i]
  have hsc : Continuous fun x => ‖s x‖ₑ ^ 2 := (ENNReal.continuous_pow 2).comp (continuous_enorm.comp s.continuous)
  haveI : BorelSpace (mixedEmbedding.mixedSpace F) := inferInstance
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := inferInstance
  haveI h1 : (volume : Measure (mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := inferInstance
  haveI h2 : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hc : (∫⁻ x, ‖s x‖ₑ ^ 2) ≠ 0 := by
    intro hc
    have hae := (lintegral_eq_zero_iff' hsc.aemeasurable).1 hc
    have heq := (Continuous.ae_eq_iff_eq volume hsc continuous_const).1 hae
    have : ‖s x0‖ₑ ^ 2 = 0 := congrFun heq x0
    rw [pow_eq_zero_iff two_ne_zero, enorm_eq_zero, hs] at this
    exact ha0 this
  have hμV : μ V ≠ 0 := hVo.measure_ne_zero μ ⟨y0, fun i => rfl⟩
  have hle : (∫⁻ x, ‖s x‖ₑ ^ 2) * μ V ≤ l2A F μ D := by
    rw [← lintegral_indicator_const hVo.measurableSet]
    unfold l2A
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ V
    · rw [Set.indicator_of_mem hy]
      exact le_of_eq (lintegral_congr fun x => by rw [hV y hy x])
    · rw [Set.indicator_of_notMem hy]; exact bot_le
  rw [h0] at hle
  exact mul_ne_zero hc hμV (le_antisymm hle bot_le)

end GlobalTheory.WeilL2Words
end
