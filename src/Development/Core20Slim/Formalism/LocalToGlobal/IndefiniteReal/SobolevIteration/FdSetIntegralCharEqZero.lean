module

public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FuncSt
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Order.Real

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Formalism.IndefR.Tow

section Gen

theorem fd_measure_le_of_cover {V : Type*} [AddCommGroup V] [MeasurableSpace V] {μ : Measure V}
    {Λ : AddSubgroup V} [Countable Λ] [MeasurableConstVAdd Λ V] [VAddInvariantMeasure Λ V μ] {𝓕 : Set V}
    (h𝓕 : IsAddFundamentalDomain Λ 𝓕 μ) {K : Set V}
    (hK : ∀ y, ∃ g ∈ Λ, g + y ∈ K) : μ 𝓕 ≤ μ K := by
  rw [h𝓕.measure_eq_tsum K]
  calc μ 𝓕 = μ (⋃ g : Λ, (g +ᵥ K) ∩ 𝓕) := by
        congr 1
        ext y
        simp only [Set.mem_iUnion, Set.mem_inter_iff]
        constructor
        · intro hy
          obtain ⟨g, hg, hgK⟩ := hK y
          refine ⟨⟨-g, neg_mem hg⟩, ?_, hy⟩
          refine ⟨g + y, hgK, ?_⟩
          show -g + (g + y) = y
          abel
        · rintro ⟨_, _, hy⟩; exact hy
    _ ≤ ∑' g : Λ, μ ((g +ᵥ K) ∩ 𝓕) := measure_iUnion_le _

theorem fd_measure_lt_top {V : Type*} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] {μ : Measure V}
    [IsFiniteMeasureOnCompacts μ] {Λ : AddSubgroup V} [Countable Λ] [MeasurableConstVAdd Λ V]
    [VAddInvariantMeasure Λ V μ] {𝓕 : Set V} (h𝓕 : IsAddFundamentalDomain Λ 𝓕 μ) {K : Set V} (hKc : IsCompact K)
    (hK : ∀ y, ∃ g ∈ Λ, g + y ∈ K) : μ 𝓕 < ⊤ :=
  (fd_measure_le_of_cover h𝓕 hK).trans_lt hKc.measure_lt_top

variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V]
  [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure] {Λ : AddSubgroup V} [Countable Λ] {𝓕 : Set V}

theorem fd_setIntegral_add (h𝓕 : IsAddFundamentalDomain Λ 𝓕 μ) {f : V → ℂ}
    (hf : ∀ g ∈ Λ, ∀ x, f (g + x) = f x) (a : V) :
    ∫ x in 𝓕, f (x + a) ∂μ = ∫ x in 𝓕, f x ∂μ := by
  have hmp := measurePreserving_add_right μ a
  have hemb : MeasurableEmbedding (fun x : V => x + a) := measurableEmbedding_addRight a
  rw [← hmp.setIntegral_image_emb hemb f 𝓕]
  have himg : (fun x : V => x + a) '' 𝓕 = a +ᵥ 𝓕 := by
    ext y
    simp only [Set.mem_image, Set.mem_vadd_set, vadd_eq_add]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, add_comm a x⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, add_comm x a⟩
  rw [himg]
  exact (h𝓕.vadd_of_comm a).setIntegral_eq h𝓕 (fun g x => hf g g.2 x)

theorem fd_setIntegral_char_eq_zero (h𝓕 : IsAddFundamentalDomain Λ 𝓕 μ) {χ : V → ℂ}
    (hmul : ∀ x y, χ (x + y) = χ x * χ y) (hΛ : ∀ g ∈ Λ, χ g = 1) {a : V} (ha : χ a ≠ 1) :
    ∫ x in 𝓕, χ x ∂μ = 0 := by
  have hper : ∀ g ∈ Λ, ∀ x, χ (g + x) = χ x := fun g hg x => by rw [hmul, hΛ g hg, one_mul]
  have h := fd_setIntegral_add h𝓕 hper a
  simp_rw [hmul] at h
  rw [integral_mul_const] at h
  have : (∫ x in 𝓕, χ x ∂μ) * (χ a - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.1 this with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.1 h0) ha

end Gen

section FDom

end FDom

section Cent

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable (F : Type) [Field F] [NumberField F]

end Cent

section Frame

open Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

end Frame

end Formalism.IndefR.Tow

end
