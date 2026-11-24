module

public import Mathlib
public import Development.Core20Slim.GroundTheory.AutomorphicForms.ReductionMahler
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Positive.Field
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Max
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

theorem eq_one_of_isCompact {G : Type*} [Group G] [TopologicalSpace G] {H : Subgroup G}
    (hH : IsCompact (H : Set G)) (f : G →* {r : ℝ // 0 < r}) (hf : Continuous fun g => (f g : ℝ))
    {h : G} (hh : h ∈ H) : f h = 1 := by
  obtain ⟨M, hM⟩ := hH.exists_bound_of_continuousOn hf.continuousOn
  have hbound : ∀ m : ℕ, (f h : ℝ) ^ m ≤ M ∧ ((f h : ℝ)⁻¹) ^ m ≤ M := fun m => by
    have h1 := hM (h ^ m) (pow_mem hh m)
    have h2 := hM ((h⁻¹) ^ m) (pow_mem (inv_mem hh) m)
    rw [map_pow, Positive.val_pow, Real.norm_eq_abs, abs_of_pos (pow_pos (f h).2 m)] at h1
    rw [map_pow, map_inv, Positive.val_pow, Positive.coe_inv, Real.norm_eq_abs,
      abs_of_pos (pow_pos (inv_pos.2 (f h).2) m)] at h2
    exact ⟨h1, h2⟩
  refine Subtype.ext ?_
  rw [Positive.val_one]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : 1 < (f h : ℝ)⁻¹ := (one_lt_inv₀ (f h).2).2 hlt
    obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop M |>.exists
    exact absurd (hbound m).2 (not_le.2 hm)
  · obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop M |>.exists
    exact absurd (hbound m).1 (not_le.2 hm)

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}










end Reduction

end

end GroundTheory.Automorphic
