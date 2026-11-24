module

public import Mathlib
public import Batteries.Logic
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Filter Topology in
theorem UpperTheory.Reformulated.B.GaloisBoundFirst.main :
    ∀ (B : ℂ → ℂ),
      Differentiable ℂ B →
        (∃ (z : ℂ), B z ≠ (0 : ℂ)) →
          ∀ (a : ℂ), ∃ (k : ℕ) (v : ℂ → ℂ), Differentiable ℂ v ∧ v a ≠ (0 : ℂ) ∧ ∀ (z : ℂ), B z = (z - a) ^ k * v z := by
  rintro B hB ⟨z0, hz0⟩ a
  have han : AnalyticOnNhd ℂ B Set.univ := hB.differentiableOn.analyticOnNhd isOpen_univ
  have hnot : ¬ ∀ᶠ z in 𝓝 a, B z = 0 := fun h => hz0
    (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a) h
      (Set.mem_univ z0))
  obtain ⟨k, g, hg, hga, hev⟩ :=
    (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff (han a (Set.mem_univ a))).2 hnot
  have hev' : ∀ᶠ z in 𝓝 a, z ≠ a → B z / (z - a) ^ k = g z := by
    filter_upwards [hev] with z hz hne
    have h0 : (z - a) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hne)
    rw [hz, smul_eq_mul]
    field_simp
  let v : ℂ → ℂ := fun z => if z = a then g a else B z / (z - a) ^ k
  have hva : v a = g a := by simp [v]
  have hvne : ∀ z, z ≠ a → v z = B z / (z - a) ^ k := fun z hz => by simp [v, hz]
  refine ⟨k, v, ?_, by rwa [hva], ?_⟩
  · intro z
    by_cases hz : z = a
    · subst hz
      have : v =ᶠ[𝓝 z] g := by
        filter_upwards [hev'] with w hw
        by_cases hwz : w = z
        · rw [hwz, hva]
        · rw [hvne w hwz, hw hwz]
      exact (hg.differentiableAt.congr_of_eventuallyEq this)
    · have hd : DifferentiableAt ℂ (fun w => B w / (w - a) ^ k) z :=
        (hB z).div (((differentiableAt_id).sub (differentiableAt_const a)).pow k)
          (pow_ne_zero _ (sub_ne_zero.2 hz))
      have : v =ᶠ[𝓝 z] fun w => B w / (w - a) ^ k := by
        filter_upwards [isOpen_ne.mem_nhds hz] with w hw
        exact hvne w hw
      exact hd.congr_of_eventuallyEq this
  · intro z
    by_cases hz : z = a
    · subst hz
      have hB0 : B z = (z - z) ^ k * g z := by
        simpa [smul_eq_mul] using hev.self_of_nhds
      rw [hva]; exact hB0
    · rw [hvne z hz]
      have h0 : (z - a) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hz)
      field_simp
