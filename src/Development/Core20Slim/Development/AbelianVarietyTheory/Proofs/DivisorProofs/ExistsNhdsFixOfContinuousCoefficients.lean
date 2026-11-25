module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Topology Filter

namespace GlobalTheory.SmoothFix

theorem eq_one_of_pow_norm_sub_one_le_half {A : Type} [NormedRing A] [NormedAlgebra ℂ A] {x : A}
    (h : ∀ m : ℕ, ‖x ^ m - 1‖ ≤ 1 / 2) : x = 1 := by
  have h1 : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖x - 1‖ ≤ ‖x ^ (2 ^ k) - 1‖ := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨y, hy⟩ : ∃ y, y = x ^ (2 ^ k) - 1 := ⟨_, rfl⟩
      have e : (2 : ℂ) • y = (x ^ (2 ^ (k + 1)) - 1) - y * y := by
        rw [pow_succ 2, pow_mul, hy, two_smul, sq]; noncomm_ring
      have h2 : 2 * ‖y‖ ≤ ‖x ^ (2 ^ (k + 1)) - 1‖ + ‖y‖ * ‖y‖ := by
        have := norm_sub_le (x ^ (2 ^ (k + 1)) - 1) (y * y)
        rw [← e, norm_smul, Complex.norm_ofNat] at this
        linarith [norm_mul_le y y]
      have h3 : ‖y‖ * ‖y‖ ≤ 1 / 2 * ‖y‖ := mul_le_mul_of_nonneg_right (hy ▸ h _) (norm_nonneg y)
      rw [← hy] at ih
      rw [pow_succ]
      linarith
  by_contra hz
  have hp : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖x - 1‖⁻¹) (show (1 : ℝ) < 3 / 2 by norm_num)
  have h4 := (h1 k).trans (h _)
  have h5 := mul_lt_mul_of_pos_right hk hp
  rw [inv_mul_cancel₀ hp.ne'] at h5
  linarith

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exists_nhds_fix : (∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s)) →
  ∀ {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) {V : Type} [AddCommGroup V] [Module ℂ V]
    (S : G → Module.End ℂ V), (∀ x ∈ H, ∀ y ∈ H, S (x * y) = S x * S y) → S 1 = 1 →
    (∀ (l : V →ₗ[ℂ] ℂ) (w : V), ContinuousOn (fun x => l (S x w)) (H : Set G)) →
    (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, K ≤ H ∧ IsCompact (K : Set G) ∧
      (∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧ ∀ x ∈ O, x ∈ H → x ∈ K) ∧ (K : Set G) ⊆ U) →
    ∀ v : V, ∃ U ∈ 𝓝 (1 : G), ∀ x ∈ U, x ∈ H → S x v = v := by
  intro hfd G _ _ H V _ _ S hmul h1 hcont hsmall v
  obtain ⟨K₀, hK₀H, hK₀c, ⟨O₀, hO₀o, hO₀1, hO₀K⟩, -⟩ := hsmall Set.univ univ_mem
  let s : Set V := (fun k => S k v) '' (K₀ : Set G)
  have hb : ∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C := by
    intro l
    obtain ⟨C, hC⟩ := hK₀c.exists_bound_of_continuousOn ((hcont l v).mono hK₀H)
    exact ⟨C, by rintro _ ⟨k, hk, rfl⟩; exact hC k hk⟩
  haveI : FiniteDimensional ℂ (Submodule.span ℂ s) := hfd s hb
  set W := Submodule.span ℂ s with hW
  have hinv : ∀ k ∈ K₀, ∀ w ∈ W, S k w ∈ W := by
    intro k hk w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k', hk', rfl⟩ := hx
      show S k (S k' v) ∈ W
      rw [← Module.End.mul_apply, ← hmul k (hK₀H hk) k' (hK₀H hk')]
      exact Submodule.subset_span ⟨k * k', K₀.mul_mem hk hk', rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact W.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact W.smul_mem c hx
  let R : K₀ → Module.End ℂ W := fun k => (S k).restrict (hinv k.1 k.2)
  have hRv : ∀ (k : K₀) (w : W), (R k w : V) = S k w := fun _ _ => rfl
  have hRpow : ∀ (k : K₀) (m : ℕ), R (k ^ m) = R k ^ m := by
    intro k m
    induction m with
    | zero =>
      ext w
      simp [hRv, h1]
    | succ m ih =>
      ext w
      rw [pow_succ, pow_succ, Module.End.mul_apply, ← ih, hRv, hRv, hRv]
      have hm : ((k ^ m : K₀) : G) ∈ H := hK₀H (k ^ m).2
      simp only [Subgroup.coe_mul]
      rw [hmul _ hm _ (hK₀H k.2), Module.End.mul_apply]
  let b := Module.finBasis ℂ W
  choose c hc using fun i => LinearMap.exists_extend (b.coord i)
  let M : G → Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ := fun x i j => c i (S x (b j))
  have hMR : ∀ k : K₀, LinearMap.toMatrixAlgEquiv b (R k) = M k := by
    intro k
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply]
    have := LinearMap.congr_fun (hc i) (R k (b j))
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply] at this
    rw [← this, hRv]
  have hR1 : R 1 = 1 := by
    ext w
    simp [hRv, h1]
  have hM1 : M 1 = 1 := by
    have := hMR 1
    rw [hR1, map_one] at this
    simpa using this.symm
  have hM : ContinuousOn M (H : Set G) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hcont (c i) (b j)
  have hN : ContinuousWithinAt (fun x => ‖M x - 1‖) (H : Set G) 1 :=
    ((hM 1 H.one_mem).sub continuousWithinAt_const).norm
  have hev : {x | ‖M x - 1‖ < 1 / 2} ∈ 𝓝[(H : Set G)] 1 :=
    hN (Iio_mem_nhds (by show ‖M 1 - 1‖ < 1 / 2; rw [hM1, sub_self, norm_zero]; norm_num))
  obtain ⟨u, hu, h1u, hsub⟩ := mem_nhdsWithin.1 hev
  obtain ⟨K, hKH, -, ⟨O, hOo, hO1, hOK⟩, hKU⟩ :=
    hsmall (u ∩ O₀) (Filter.inter_mem (hu.mem_nhds h1u) (hO₀o.mem_nhds hO₀1))
  have hvW : v ∈ W := Submodule.subset_span ⟨1, K₀.one_mem, by simp [h1]⟩
  refine ⟨O, hOo.mem_nhds hO1, fun x hxO hxH => ?_⟩
  have hxK : x ∈ K := hOK x hxO hxH
  have hxK₀ : x ∈ K₀ := hO₀K x (hKU hxK).2 (hKH hxK)
  let kk : K₀ := ⟨x, hxK₀⟩
  have hpow : ∀ m : ℕ, ‖(LinearMap.toMatrixAlgEquiv b (R kk)) ^ m - 1‖ ≤ 1 / 2 := by
    intro m
    rw [← map_pow, ← hRpow, hMR]
    have hm : x ^ m ∈ K := K.pow_mem hxK m
    have := hsub ⟨(hKU hm).1, hKH hm⟩
    exact le_of_lt (by simpa using this)
  have hone := eq_one_of_pow_norm_sub_one_le_half hpow
  rw [← map_one (LinearMap.toMatrixAlgEquiv b)] at hone
  have hRk := (LinearMap.toMatrixAlgEquiv b).injective hone
  have := congrArg Subtype.val (LinearMap.congr_fun hRk ⟨v, hvW⟩)
  simpa [hRv] using this

end GlobalTheory.SmoothFix
