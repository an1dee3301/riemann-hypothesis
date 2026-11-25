module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.TSC

theorem iteratedDeriv_sum_on {ι : Type} (s : Finset ι) {U : Set ℂ} (hU : IsOpen U) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, DifferentiableOn ℂ (f i) U) (r : ℕ) :
    (∀ i ∈ s, DifferentiableOn ℂ (iteratedDeriv r (f i)) U) ∧
    EqOn (iteratedDeriv r (fun w => ∑ i ∈ s, f i w)) (fun w => ∑ i ∈ s, iteratedDeriv r (f i) w) U := by
  induction r with
  | zero =>
    simp only [iteratedDeriv_zero]
    exact ⟨hf, fun _ _ => rfl⟩
  | succ r ih =>
    obtain ⟨hd, he⟩ := ih
    refine ⟨fun i hi => ?_, fun z hz => ?_⟩
    · rw [iteratedDeriv_succ]
      exact (hd i hi).deriv hU
    · simp only [iteratedDeriv_succ]
      have hev : iteratedDeriv r (fun w => ∑ i ∈ s, f i w) =ᶠ[𝓝 z]
          (fun w => ∑ i ∈ s, iteratedDeriv r (f i) w) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hz) he
      rw [hev.deriv_eq]
      first
        | exact deriv_fun_sum (fun i hi => (hd i hi).differentiableAt (hU.mem_nhds hz))
        | exact deriv_sum (fun i hi => (hd i hi).differentiableAt (hU.mem_nhds hz))

theorem exists_int_elem {X : Type} [MeasurableSpace X] (ν : Measure X) {V : Type} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ V) [FiniteDimensional ℂ W] (φ : X → V) (hφ : ∀ x, φ x ∈ W)
    (hint : ∀ l : V →ₗ[ℂ] ℂ, Integrable (fun x => l (φ x)) ν) :
    ∃ Φ ∈ W, ∀ l : V →ₗ[ℂ] ℂ, l Φ = ∫ x, l (φ x) ∂ν := by
  classical
  let b := Module.finBasis ℂ W
  choose cl hcl using fun j => LinearMap.exists_extend (b.coord j)
  have hc : ∀ j x, cl j (φ x) = b.repr ⟨φ x, hφ x⟩ j := by
    intro j x
    have := LinearMap.congr_fun (hcl j) ⟨φ x, hφ x⟩
    simpa using this
  have hrepr : ∀ x, φ x = ∑ j, cl j (φ x) • (b j : V) := by
    intro x
    have h1 := b.sum_repr ⟨φ x, hφ x⟩
    have h2 := congrArg (fun w : W => (w : V)) h1
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    simp only [hc]
    exact h2.symm
  refine ⟨∑ j, (∫ x, cl j (φ x) ∂ν) • (b j : V), Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2,
    fun l => ?_⟩
  have e1 : ∀ x, l (φ x) = ∑ j, cl j (φ x) * l (b j) := by
    intro x
    conv_lhs => rw [hrepr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul, smul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul]
  simp_rw [e1]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const]
  · intro j _
    exact (hint (cl j)).mul_const _

end PositivityTheory.Rg.Sw.AbsSt.TSC
