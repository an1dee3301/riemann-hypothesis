module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
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
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Topology.PartialHomeomorph.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix

namespace GlobalTheory

theorem sq_scalar_character : ∀ (G G' M H : Type) [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] [Group M]
    [TopologicalSpace M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Nontrivial H] (pr : G' →* M) (s : G →* M)
    (om : G' →* (H ≃ₗᵢ[ℂ] H)) (ω : G →* (H ≃ₗᵢ[ℂ] H)) (ε : G'), IsCoveringMap pr → Function.Surjective pr →
    (∀ g, pr g = 1 → g = 1 ∨ g = ε) → (∀ v, om ε v = -v) → Continuous s → (∀ v, Continuous fun g => om g v) →
    (∀ v, Continuous fun g => ω g v) → (∀ g g', pr g' = s g → ∃ a : ℂ, ∀ v, ω g v = a • om g' v) →
    ∃ η : G → ℂ, (∀ g h, η (g * h) = η g * η h) ∧ Continuous η ∧ (∀ g, η g ≠ 0) ∧
      ∀ g g' (a : ℂ), pr g' = s g → (∀ v, ω g v = a • om g' v) → a ^ 2 = η g := by
  intro G G' M H _ _ _ _ _ _ _ _ _ pr s om ω ε hcov hsurj hker hε hs hom hω hrel
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : H)
  have huniq : ∀ g (g₁ g₂ : G') (a b : ℂ), pr g₁ = s g → pr g₂ = s g →
      (∀ v, ω g v = a • om g₁ v) → (∀ v, ω g v = b • om g₂ v) → a ^ 2 = b ^ 2 := by
    intro g g₁ g₂ a b h₁ h₂ ha hb
    have hw : om g₁ v₀ ≠ 0 := by
      intro h; apply hv₀; exact (om g₁).map_eq_zero_iff.mp h
    have hk : pr (g₁⁻¹ * g₂) = 1 := by simp [map_mul, map_inv, h₁, h₂]
    rcases hker _ hk with h | h
    · have h2 : g₂ = g₁ := by rw [← mul_inv_cancel_left g₁ g₂, h, mul_one]
      subst h2
      have : a • om g₂ v₀ = b • om g₂ v₀ := by rw [← ha, ← hb]
      have hab : a = b := smul_left_injective ℂ hw this
      rw [hab]
    · have h2 : g₂ = g₁ * ε := by rw [← h, mul_inv_cancel_left]
      have : a • om g₁ v₀ = (-b) • om g₁ v₀ := by
        rw [← ha, hb, h2, map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hε,
          map_neg, smul_neg, neg_smul]
      have hab : a = -b := smul_left_injective ℂ hw this
      rw [hab]; ring
  have hlift : ∀ g, ∃ g', pr g' = s g := fun g => hsurj (s g)
  choose L hL using hlift
  choose A hA using fun g => hrel g (L g) (hL g)
  refine ⟨fun g => A g ^ 2, ?_, ?_, ?_, ?_⟩
  · intro g h
    have hmul : pr (L g * L h) = s (g * h) := by simp [map_mul, hL]
    have hsc : ∀ v, ω (g * h) v = (A g * A h) • om (L g * L h) v := by
      intro v
      rw [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hA h, LinearIsometryEquiv.map_smul,
        hA g, map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, smul_smul, mul_comm (A h)]
    have := huniq (g * h) (L (g * h)) (L g * L h) _ _ (hL _) hmul (hA _) hsc
    simp only
    rw [this]; ring
  · rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨e, he, hpe⟩ := hcov.isLocalHomeomorph (L g₀)
    have hopen : IsOpen (s ⁻¹' e.target) := e.open_target.preimage hs
    have hmem : g₀ ∈ s ⁻¹' e.target := by
      show s g₀ ∈ e.target
      rw [← hL g₀, hpe]; exact e.map_source he
    let f : G → ℂ := fun g => (inner ℂ (om (e.symm (s g)) v₀) (ω g v₀) / inner ℂ v₀ v₀) ^ 2
    have hf : ContinuousAt f g₀ := by
      have h1 : ContinuousAt (fun g => om (e.symm (s g)) v₀) g₀ :=
        (hom v₀).continuousAt.comp ((e.continuousAt_symm hmem).comp hs.continuousAt)
      exact ((h1.inner (hω v₀).continuousAt).div_const _).pow 2
    refine hf.congr ?_
    filter_upwards [hopen.mem_nhds hmem] with g hg
    have hpr : pr (e.symm (s g)) = s g := by rw [hpe]; exact e.right_inv hg
    obtain ⟨c, hc⟩ := hrel g _ hpr
    have hcval : c = inner ℂ (om (e.symm (s g)) v₀) (ω g v₀) / inner ℂ v₀ v₀ := by
      rw [hc, inner_smul_right, LinearIsometryEquiv.inner_map_map, mul_div_assoc,
        div_self (inner_self_ne_zero.2 hv₀), mul_one]
    show f g = A g ^ 2
    simp only [f]
    rw [← hcval]
    exact huniq g _ _ c (A g) hpr (hL g) hc (hA g)
  · intro g
    refine pow_ne_zero 2 ?_
    intro h0
    have := hA g v₀
    rw [h0, zero_smul] at this
    exact hv₀ ((ω g).map_eq_zero_iff.mp this)
  · intro g g' a hg' ha
    exact huniq g g' (L g) a (A g) hg' (hL g) ha (hA g)

end GlobalTheory
