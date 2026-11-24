module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFactorialBound
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverUpqClosureExpTopAndCartanStatement
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

noncomputable section
namespace GlobalTheory.AnalyticDense
open GlobalTheory.FockTensor

theorem inner_orbit_eq_zero {p q : ℕ} {T : GrpData p q} (D : DSRep T) {Y : Mat p q}
    (hY : Y ∈ upq p q) (y : D.HK.V) {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hb : ∀ k : ℕ, ‖D.ι ((D.HK.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ))
    (w : D.U.H) (hw : ∀ v, inner ℂ w (D.ι v) = 0) (t : ℝ) :
    inner ℂ w (D.U.π (T.expt (t • Y)) (D.ι y)) = 0 := by

  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ → ℂ, g = fun k s =>
      inner ℂ w (D.U.π (T.expt (s • Y)) (D.ι ((D.HK.act Y ^ k) y))) := ⟨_, rfl⟩
  have hd : ∀ k s, HasDerivAt (g k) (g (k + 1) s) s := by
    intro k s
    have h1 := hasDerivAt_orbit D.U hY (D.der Y hY ((D.HK.act Y ^ k) y)) s
    have h2 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1
    have e : (D.HK.act Y ^ (k + 1)) y = D.HK.act Y ((D.HK.act Y ^ k) y) := by
      rw [pow_succ']; rfl
    subst hg
    simp only [e]
    exact h2

  have hb' : ∀ k s, ‖g k s‖ ≤ (‖w‖ * C) * ρ ^ k * (k.factorial : ℝ) := by
    intro k s
    subst hg
    calc ‖inner ℂ w (D.U.π (T.expt (s • Y)) (D.ι ((D.HK.act Y ^ k) y)))‖
        ≤ ‖w‖ * ‖D.U.π (T.expt (s • Y)) (D.ι ((D.HK.act Y ^ k) y))‖ := norm_inner_le_norm _ _
      _ = ‖w‖ * ‖D.ι ((D.HK.act Y ^ k) y)‖ := by rw [D.U.isom]
      _ ≤ ‖w‖ * (C * ρ ^ k * (k.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left (hb k) (norm_nonneg w)
      _ = ‖w‖ * C * ρ ^ k * (k.factorial : ℝ) := by ring

  have h0 : ∀ k, g k 0 = 0 := by
    intro k
    subst hg
    simp only [zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply]
    exact hw _
  have key := GlobalTheory.FactorialJet.eq_zero_of_factorial_bound ℂ g (‖w‖ * C) ρ
    (mul_nonneg (norm_nonneg w) hC) hρ hd hb' h0 0 t
  subst hg
  simpa using key

theorem orbit_mem_closure {p q : ℕ} {T : GrpData p q} (D : DSRep T) {Y : Mat p q}
    (hY : Y ∈ upq p q)
    (hb : ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧
      ∀ k : ℕ, ‖D.ι ((D.HK.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ))
    (t : ℝ) (x : D.U.H) (hx : x ∈ (LinearMap.range D.ι).topologicalClosure) :
    D.U.π (T.expt (t • Y)) x ∈ (LinearMap.range D.ι).topologicalClosure := by

  have hsub : LinearMap.range D.ι ≤ (LinearMap.range D.ι).topologicalClosure.comap
      ((D.U.π (T.expt (t • Y)) : D.U.H →L[ℂ] D.U.H) : D.U.H →ₗ[ℂ] D.U.H) := by
    intro z hz
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hz
    obtain ⟨C, ρ, hC, hρ, hk⟩ := hb v
    rw [Submodule.mem_comap, ← Submodule.orthogonal_orthogonal_eq_closure,
      Submodule.mem_orthogonal]
    intro u hu
    rw [ContinuousLinearMap.coe_coe]
    exact inner_orbit_eq_zero D hY v hC hρ hk u
      (fun z => (Submodule.mem_orthogonal' _ _).1 hu _ (LinearMap.mem_range_self _ z)) t
  have hcl : IsClosed (((LinearMap.range D.ι).topologicalClosure.comap
      ((D.U.π (T.expt (t • Y)) : D.U.H →L[ℂ] D.U.H) : D.U.H →ₗ[ℂ] D.U.H) :
        Submodule ℂ D.U.H) : Set D.U.H) :=
    (Submodule.isClosed_topologicalClosure _).preimage (D.U.π _).continuous
  exact Submodule.topologicalClosure_minimal _ hsub hcl hx

theorem dense_range_of_factorial_bound : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q)
    (D : DSRep T), Nontrivial D.HK.V →
    (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧
      ∀ k : ℕ, ‖D.ι ((D.HK.act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) →
    Dense (Set.range D.ι) := by
  intro p q hpq T D hnt hb

  have hgen : ∀ g ∈ T.expt '' upq p q, ∀ x ∈ (LinearMap.range D.ι).topologicalClosure,
      D.U.π g x ∈ (LinearMap.range D.ι).topologicalClosure ∧
      D.U.π g⁻¹ x ∈ (LinearMap.range D.ι).topologicalClosure := by
    rintro _ ⟨Y, hY, rfl⟩ x hx
    have hneg : (T.expt Y)⁻¹ = T.expt ((-1 : ℝ) • Y) := by
      have h := T.expt_add Y hY (-1) 1
      have e : ((-1 : ℝ) + 1) = 0 := by norm_num
      rw [e, zero_smul, T.expt_zero, one_smul] at h
      exact (eq_inv_of_mul_eq_one_left h.symm).symm
    refine ⟨?_, ?_⟩
    · have h1 := orbit_mem_closure D hY (hb Y hY) 1 x hx
      rwa [one_smul] at h1
    · rw [hneg]
      exact orbit_mem_closure D hY (hb Y hY) (-1) x hx

  have hall : ∀ g : T.G, ∀ x ∈ (LinearMap.range D.ι).topologicalClosure,
      D.U.π g x ∈ (LinearMap.range D.ι).topologicalClosure ∧
      D.U.π g⁻¹ x ∈ (LinearMap.range D.ι).topologicalClosure := by
    intro g
    have hg : g ∈ Subgroup.closure (T.expt '' upq p q) := by
      rw [(GlobalTheory.T.coverUpq_closure_exp_top_and_cartan p q hpq T).1]
      exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem a ha => exact hgen a ha
    | one =>
      intro x hx
      rw [inv_one, map_one, ContinuousLinearMap.one_apply]
      exact ⟨hx, hx⟩
    | mul a b _ _ ha hb' =>
      intro x hx
      refine ⟨?_, ?_⟩
      · rw [map_mul, ContinuousLinearMap.mul_apply]
        exact (ha _ (hb' x hx).1).1
      · rw [mul_inv_rev, map_mul, ContinuousLinearMap.mul_apply]
        exact (hb' _ (ha x hx).2).2
    | inv a _ ha =>
      intro x hx
      rw [inv_inv]
      exact ⟨(ha x hx).2, (ha x hx).1⟩

  rcases D.3 _ (Submodule.isClosed_topologicalClosure _) (fun g x hx => (hall g x hx).1) with h | h
  · exfalso
    obtain ⟨v, hv⟩ := exists_ne (0 : D.HK.V)
    have h1 : D.ι v ∈ (LinearMap.range D.ι).topologicalClosure :=
      Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ v)
    rw [h, Submodule.mem_bot] at h1
    exact hv (D.9 (h1.trans (map_zero D.ι).symm))
  · have e : ((LinearMap.range D.ι : Submodule ℂ D.U.H) : Set D.U.H) = Set.range D.ι := by
      ext z
      simp
    rw [← e]
    exact Submodule.dense_iff_topologicalClosure_eq_top.2 h

end GlobalTheory.AnalyticDense
