module

public import Mathlib
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Logic.Pairwise
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open MeasureTheory

namespace GlobalTheory

theorem summable_norm_coset_out (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G)
    (hK : IsOpen (K : Set G)) (hμ : μ K = 1) (F : G → ℂ)
    (hF : ∀ g, ∀ k ∈ K, F (g * k) = F g) (hint : Integrable F μ) :
    Summable (fun x : G ⧸ K => ‖F x.out‖) := by
  classical
  set C : G ⧸ K → Set G := fun x => (fun y => x.out⁻¹ * y) ⁻¹' (K : Set G) with hCdef
  have hCmeas : ∀ x, MeasurableSet (C x) := fun x =>
    (hK.preimage (continuous_const.mul continuous_id)).measurableSet
  have hCμ : ∀ x, μ (C x) = 1 := by
    intro x
    simp only [C]
    rw [measure_preimage_mul]; exact hμ
  have hconst : ∀ x, ∀ y ∈ C x, F y = F x.out := by
    intro x y hy
    have hy' : x.out⁻¹ * y ∈ K := hy
    have := hF x.out _ hy'
    simpa using this
  have hmk : ∀ x, ∀ y ∈ C x, (QuotientGroup.mk y : G ⧸ K) = x := by
    intro x y hy
    have hy' : x.out⁻¹ * y ∈ K := hy
    have h1 : (QuotientGroup.mk y : G ⧸ K) = QuotientGroup.mk x.out :=
      (QuotientGroup.eq.mpr hy').symm
    rw [h1]; exact Quotient.out_eq x
  have hdisj : Pairwise (Function.onFun Disjoint C) := by
    intro x y hxy
    rw [Function.onFun, Set.disjoint_left]
    intro z hzx hzy
    exact hxy ((hmk x z hzx).symm.trans (hmk y z hzy))
  have hnorm : Integrable (fun y => ‖F y‖) μ := hint.norm
  have hterm : ∀ x, ∫ y in C x, ‖F y‖ ∂μ = ‖F x.out‖ := by
    intro x
    rw [setIntegral_congr_fun (hCmeas x) (g := fun _ => ‖F x.out‖) (fun y hy => by
      simp only; rw [hconst x y hy])]
    rw [setIntegral_const]
    simp [Measure.real, hCμ x]
  refine summable_of_sum_le (c := ∫ y, ‖F y‖ ∂μ) (fun x => norm_nonneg _) ?_
  intro S
  calc ∑ x ∈ S, ‖F x.out‖ = ∑ x ∈ S, ∫ y in C x, ‖F y‖ ∂μ := by
        simp only [hterm]
    _ = ∫ y in ⋃ x ∈ S, C x, ‖F y‖ ∂μ := by
        rw [integral_biUnion_finset S (fun x _ => hCmeas x) (hdisj.set_pairwise _)
          (fun x _ => hnorm.integrableOn)]
    _ ≤ ∫ y, ‖F y‖ ∂μ :=
        setIntegral_le_integral hnorm (Filter.Eventually.of_forall (fun y => norm_nonneg _))

end GlobalTheory
