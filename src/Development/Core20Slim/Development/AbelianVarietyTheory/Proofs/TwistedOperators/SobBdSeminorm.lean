module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.Order.Lemmas
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
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Hom.Basic
public import Mathlib.Algebra.Order.Hom.GroupNorm
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.L2.Theta Formalism.MainNotions.S GlobalTheory.SmoothGlob

namespace GlobalTheory.FactorExtension

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem sobNorm_nonneg (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : List (List (Matrix (Fin n) (Fin n) ℂ)))
    (w : H) : 0 ≤ sobNorm σ S w :=
  List.sum_nonneg fun x hx => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _

theorem sobNorm_append (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S S' : List (List (Matrix (Fin n) (Fin n) ℂ)))
    (w : H) : sobNorm σ (S ++ S') w = sobNorm σ S w + sobNorm σ S' w := by
  simp [sobNorm, List.map_append, List.sum_append]

theorem sob_max {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {S S' : List (List (Matrix (Fin n) (Fin n) ℂ))}
    {C C' a a' : ℝ} {w : H} (h : a ≤ C * sobNorm σ S w) (h' : a' ≤ C' * sobNorm σ S' w) :
    a + a' ≤ max |C| |C'| * sobNorm σ (S ++ S') w ∧ max a a' ≤ max |C| |C'| * sobNorm σ (S ++ S') w := by
  have h0 := sobNorm_nonneg σ S w
  have h0' := sobNorm_nonneg σ S' w
  have e1 : C * sobNorm σ S w ≤ max |C| |C'| * sobNorm σ S w :=
    mul_le_mul_of_nonneg_right ((le_abs_self C).trans (le_max_left _ _)) h0
  have e2 : C' * sobNorm σ S' w ≤ max |C| |C'| * sobNorm σ S' w :=
    mul_le_mul_of_nonneg_right ((le_abs_self C').trans (le_max_right _ _)) h0'
  have hm : 0 ≤ max |C| |C'| := (abs_nonneg C).trans (le_max_left _ _)
  rw [sobNorm_append, mul_add]
  refine ⟨by linarith, max_le ?_ ?_⟩
  · nlinarith [mul_nonneg hm h0']
  · nlinarith [mul_nonneg hm h0]

variable {E : Type} [AddCommGroup E] [Module ℂ E]

def sobBd (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (p : ℕ → Seminorm ℂ E) :
    Submodule ℂ (H →ₗ[ℂ] E) where
  carrier := {L | ∀ i, ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) ∧
      ∀ w, SmoothVec (lieSet ε) σ w → p i (L w) ≤ C * sobNorm σ S w}
  zero_mem' := fun i => ⟨[], 0, by simp, fun w _ => by simp⟩
  add_mem' := by
    intro L L' hL hL' i
    obtain ⟨S, C, hS, h⟩ := hL i
    obtain ⟨S', C', hS', h'⟩ := hL' i
    refine ⟨S ++ S', max |C| |C'|, fun l hl => ?_, fun w hw => ?_⟩
    · rcases List.mem_append.1 hl with hl | hl
      · exact hS l hl
      · exact hS' l hl
    · exact (map_add_le_add (p i) _ _).trans (sob_max (h w hw) (h' w hw)).1
  smul_mem' := by
    intro c L hL i
    obtain ⟨S, C, hS, h⟩ := hL i
    refine ⟨S, ‖c‖ * C, hS, fun w hw => ?_⟩
    rw [LinearMap.smul_apply, map_smul_eq_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h w hw) (norm_nonneg c)

theorem sobBd_congr {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {p : ℕ → Seminorm ℂ E}
    {L L' : H →ₗ[ℂ] E} (hL : L ∈ sobBd ε σ p) (h : ∀ w, SmoothVec (lieSet ε) σ w → L' w = L w) :
    L' ∈ sobBd ε σ p := fun i => by
  obtain ⟨S, C, hS, hb⟩ := hL i
  exact ⟨S, C, hS, fun w hw => by rw [h w hw]; exact hb w hw⟩

theorem sobBd_seminorm [TopologicalSpace E] {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {p : ℕ → Seminorm ℂ E} (hp : WithSeminorms p) {L : H →ₗ[ℂ] E} (hL : L ∈ sobBd ε σ p) (q : Seminorm ℂ E)
    (hq : Continuous q) : ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) ∧
      ∀ w, SmoothVec (lieSet ε) σ w → q (L w) ≤ C * sobNorm σ S w := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous hp q hq
  have key : ∀ t : Finset ℕ, ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ),
      (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) ∧ ∀ w, SmoothVec (lieSet ε) σ w → (t.sup p) (L w) ≤ C * sobNorm σ S w := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨[], 0, by simp, fun w _ => by simp⟩
    | insert i t _ ih =>
      obtain ⟨S, C, hS, h⟩ := ih
      obtain ⟨S', C', hS', h'⟩ := hL i
      refine ⟨S' ++ S, max |C'| |C|, fun l hl => ?_, fun w hw => ?_⟩
      · rcases List.mem_append.1 hl with hl | hl
        · exact hS' l hl
        · exact hS l hl
      · rw [Finset.sup_insert, Seminorm.sup_apply]
        exact (sob_max (h' w hw) (h w hw)).2
  obtain ⟨S, C', hS, h⟩ := key s
  refine ⟨S, C * C', hS, fun w hw => ?_⟩
  calc q (L w) ≤ (C • s.sup p) (L w) := hC _
    _ = C * (s.sup p) (L w) := rfl
    _ ≤ C * (C' * sobNorm σ S w) := mul_le_mul_of_nonneg_left (h w hw) C.2
    _ = C * C' * sobNorm σ S w := by ring

theorem sobBd_comp [TopologicalSpace E] [IsTopologicalAddGroup E] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {p : ℕ → Seminorm ℂ E} (hp : WithSeminorms p) {L : H →ₗ[ℂ] E}
    (hL : L ∈ sobBd ε σ p) (e : E →L[ℂ] E) : (e : E →ₗ[ℂ] E) ∘ₗ L ∈ sobBd ε σ p := fun i =>
  sobBd_seminorm hp hL ((p i).comp (e : E →ₗ[ℂ] E))
    ((hp.continuous_seminorm i).comp e.continuous)

theorem dRep_comm [TopologicalSpace E] [T2Space E] {ε : Fin n → Bool} {p : ℕ → Seminorm ℂ E}
    {π dπ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)} (h : IsSmoothModRep ε p π dπ) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieSet ε) (e : E →L[ℂ] E)
    (he : ∀ t : ℝ, e.comp (π (NormedSpace.exp (t • X))) = (π (NormedSpace.exp (t • X))).comp e) :
    e.comp (dπ X) = (dπ X).comp e := by
  ext v
  have h1 := h.hasDRep X hX (e v)
  have h0 := h.hasDRep X hX v
  unfold HasDRep at h1 h0
  have h2 := (e.continuous.tendsto _).comp h0
  have h3 : Filter.Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) • (π (NormedSpace.exp (t • X)) (e v) - e v))
      (nhdsWithin 0 {0}ᶜ) (nhds (e (dπ X v))) := by
    refine h2.congr fun t => ?_
    have := congrArg (fun f : E →L[ℂ] E => f v) (he t)
    simp only [ContinuousLinearMap.comp_apply] at this
    simp only [Function.comp, map_smul, map_sub, this]
  exact tendsto_nhds_unique h3 h1

end GlobalTheory.FactorExtension

end
