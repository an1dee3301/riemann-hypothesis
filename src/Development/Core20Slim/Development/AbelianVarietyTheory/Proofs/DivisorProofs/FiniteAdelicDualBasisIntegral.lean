module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
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
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.NNReal.Star
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilL2Words

open MeasureTheory

theorem enorm_sum_mul_sq_le {m : ℕ} (a b : Fin m → ℂ) :
    ‖∑ i, a i * b i‖ₑ ^ 2 ≤ (∑ i, ‖b i‖ₑ ^ 2) * ∑ i, ‖a i‖ₑ ^ 2 := by
  have h1 : ‖∑ i, a i * b i‖₊ ≤ ∑ i, ‖b i‖₊ * ‖a i‖₊ := by
    refine (nnnorm_sum_le _ _).trans (le_of_eq ?_)
    simp [nnnorm_mul, mul_comm]
  have h2 : ‖∑ i, a i * b i‖₊ ^ 2 ≤ (∑ i, ‖b i‖₊ ^ 2) * ∑ i, ‖a i‖₊ ^ 2 :=
    (pow_le_pow_left₀ (by positivity) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  simp only [enorm_eq_nnnorm]
  exact_mod_cast h2

theorem slice_le_l2A (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (m : ℕ)
    (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (yy : Fin m → (κ → FiniteAdeleRing (𝓞 F) F))
    (hg : ∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) (hyy : ∀ i j, g i (yy j) = if i = j then 1 else 0)
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _))
    (hμ : @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (y : κ → FiniteAdeleRing (𝓞 F) F) : ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2 ≤
        C * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
  have hmeas : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Measurable fun x => ‖f x‖ₑ ^ 2 :=
    fun f => by
      haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
      exact (f.continuous.measurable.enorm).pow_const 2
  letI : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI := hμ
  have hev : ∀ (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) x y',
      (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y') = ∑ i, f i x * g i y' := by
    intro f x y'
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => GlobalTheory.WeilCont.pureA_adeleJoin F _ _ x y'

  let U : Fin m → Set (κ → FiniteAdeleRing (𝓞 F) F) := fun j => ⋂ i, {y' | g i y' = g i (yy j)}
  have hUo : ∀ j, IsOpen (U j) := fun j => isOpen_iInter_of_finite fun i => (hg i).1.isOpen_fiber _
  have hUm : ∀ j, yy j ∈ U j := fun j => Set.mem_iInter.2 fun i => rfl
  have hUv : ∀ j, ∀ y' ∈ U j, ∀ i, g i y' = if i = j then 1 else 0 := fun j y' hy' i => by
    rw [← hyy]; exact Set.mem_iInter.1 hy' i
  have hU0 : ∀ j, μ (U j) ≠ 0 := fun j => (hUo j).measure_ne_zero μ ⟨_, hUm j⟩
  have hUt : ∀ j, μ (U j) ≠ ⊤ := by
    intro j
    refine ne_top_of_le_ne_top ((hg j).2.isCompact.measure_lt_top).ne (measure_mono ?_)
    intro y' hy'
    apply subset_tsupport
    rw [Function.mem_support, hUv j y' hy' j, if_pos rfl]
    exact one_ne_zero
  have hB : (∑ i, ‖g i y‖ₑ ^ 2) ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ => ENNReal.pow_ne_top enorm_ne_top
  refine ⟨(∑ i, ‖g i y‖ₑ ^ 2) * ∑ j, (μ (U j))⁻¹, ENNReal.mul_ne_top hB
    (ENNReal.sum_ne_top.2 fun j _ => ENNReal.inv_ne_top.2 (hU0 j)), ?_⟩
  intro f
  have hA : ∀ j, ∫⁻ x, ‖f j x‖ₑ ^ 2 ≤ (μ (U j))⁻¹ * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
    intro j
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl (hU0 j)) (Or.inl (hUt j))]
    have e : ∫⁻ y' in U j, (∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y')‖ₑ ^ 2) ∂μ
        = ∫⁻ y' in U j, (∫⁻ x, ‖f j x‖ₑ ^ 2) ∂μ := by
      refine setLIntegral_congr_fun (hUo j).measurableSet (fun y' hy' => ?_)
      refine lintegral_congr fun x => ?_
      rw [hev, Finset.sum_eq_single j]
      · rw [hUv j y' hy' j, if_pos rfl, mul_one]
      · intro i _ hij
        rw [hUv j y' hy' i, if_neg hij, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [setLIntegral_const] at e
    rw [← e]
    exact setLIntegral_le_lintegral _ _
  calc ∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2
      ≤ ∫⁻ x, (∑ i, ‖g i y‖ₑ ^ 2) * ∑ i, ‖f i x‖ₑ ^ 2 := by
        refine lintegral_mono fun x => ?_
        rw [hev]
        exact enorm_sum_mul_sq_le _ _
    _ = (∑ i, ‖g i y‖ₑ ^ 2) * ∑ i, ∫⁻ x, ‖f i x‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ hB, lintegral_finsetSum]
        intro i _
        exact hmeas (f i)
    _ ≤ (∑ i, ‖g i y‖ₑ ^ 2) * ∑ j, (μ (U j))⁻¹ * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
        gcongr with j
        exact hA j
    _ = _ := by rw [← Finset.sum_mul, mul_assoc]

end GlobalTheory.WeilL2Words

end
