module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open Filter Topology

namespace GlobalTheory.CompanionTheory.RgEis


open PositivityTheory.RgEis in
theorem cross_stage_pos : PositivityTheory.RgEis.PiLocalization₂ → ∀ (G : Type) [Group G] (Γ Q P : Subgroup G) (ξ lam : G → ℝ) (t : ℝ),
    P ≤ Q → (∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x) → (∀ γ ∈ Γ, γ ∈ P → ∀ x, lam (γ * x) = lam x) →
    PositivityTheory.RgEis.Conv Γ P (fun x => lam x + t * ξ x) → ∀ g : G,
    Summable fun r : PositivityTheory.RgEis.Cos (Γ ⊓ Q) Γ => Real.exp (t * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos (Γ ⊓ Q) P lam (PositivityTheory.RgEis.rep r * g) := by
  open PositivityTheory.RgEis in
  intro hS G _ Γ Q P ξ lam t hPQ hξ hlam hc g
  have key := (hS G ℝ P (Γ ⊓ Q) Γ (fun x => Real.exp (lam x + t * ξ x)) inf_le_left
    (fun γ h1 h2 => ⟨h1, hPQ h2⟩)
    (fun γ h1 h2 x => by
      show Real.exp (lam (γ * x) + t * ξ (γ * x)) = Real.exp (lam x + t * ξ x)
      rw [hlam γ h1 h2 x, hξ γ h1 (hPQ h2) x]) g
    (by
      have h := hc g
      refine h.congr (fun q => ?_)
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)])).2.1
  refine key.congr (fun r => ?_)
  rw [pos, ← tsum_mul_left]
  refine tsum_congr (fun q => ?_)
  have hq : rep q ∈ Γ ⊓ Q := (Quotient.out q).2
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hξ _ hq.1 hq.2, ← Real.exp_add, add_comm]

end GlobalTheory.CompanionTheory.RgEis
