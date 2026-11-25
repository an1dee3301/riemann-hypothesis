module

public import Mathlib
public import Batteries.Logic
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GlobalTheory

open Complex

theorem mem_closure_of_forall_dual_vanish :
    ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p → ∀ (Z : Submodule ℂ E) (x : E),
    (∀ f : E →L[ℂ] ℂ, (∀ z ∈ Z, f z = 0) → f x = 0) → x ∈ closure (Z : Set E) := by
  intro E _ _ _ _ p hp Z x h
  haveI := hp.continuousSMul
  haveI : LocallyConvexSpace ℝ E := hp.toLocallyConvexSpace
  by_contra hx
  rw [← Z.topologicalClosure_coe] at hx
  obtain ⟨f, u, hfx, hf⟩ := RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ)
    ((Z.topologicalClosure.restrictScalars ℝ).convex) Z.isClosed_topologicalClosure hx
  simp only [RCLike.re_to_complex] at hfx hf
  have hre : ∀ w ∈ Z, (f w).re = 0 := by
    intro w hw
    by_contra hne
    set t : ℝ := (u - 1) / (f w).re
    have hmem : ((t : ℂ) • w) ∈ Z.topologicalClosure :=
      Z.le_topologicalClosure (Z.smul_mem _ hw)
    have h1 := hf _ hmem
    rw [map_smul, smul_eq_mul, Complex.re_ofReal_mul] at h1
    have : t * (f w).re = u - 1 := by
      simp only [t]; field_simp
    linarith
  have hvan : ∀ z ∈ Z, f z = 0 := by
    intro z hz
    have h1 := hre z hz
    have h2 := hre (Complex.I • z) (Z.smul_mem _ hz)
    rw [map_smul, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im] at h2
    apply Complex.ext
    · simpa using h1
    · simp at h2; simpa using h2
  have h0 := hf 0 (Z.topologicalClosure.zero_mem)
  have hfx0 := h f hvan
  rw [map_zero] at h0
  rw [hfx0] at hfx
  simp at h0 hfx
  linarith

end GlobalTheory
