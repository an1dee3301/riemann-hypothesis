module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntIndMemSB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Max
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.CharSep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem norm_le_one (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) (x : k) : ‖ψ0 x‖ ≤ 1 := by
  obtain ⟨B, hB⟩ := (SplitWeil.isCompact_int k).exists_bound_of_continuousOn
    (f := fun y => ψ0 (x * y)) (hc.comp (continuous_const.mul continuous_id)).continuousOn
  have hpow : ∀ m : ℕ, ‖ψ0 x‖ ^ m ≤ B := fun m => by
    have hm : ((m : k)) ∈ 𝒪[k] := by
      simpa using (Subring.natCast_mem (𝒪[k]) m)
    have := hB _ hm
    rwa [show x * (m : k) = m • x by rw [nsmul_eq_mul, mul_comm], AddChar.map_nsmul_eq_pow, norm_pow] at this
  by_contra h
  push_neg at h
  obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt h).eventually_gt_atTop B |>.exists
  exact absurd (hpow m) (not_le.mpr hm)

theorem norm_eq_one (ψ0 : AddChar k ℂ) (hc : Continuous ψ0) (x : k) : ‖ψ0 x‖ = 1 := by
  have h1 := norm_le_one ψ0 hc x
  have h2 := norm_le_one ψ0 hc (-x)
  have hm : ψ0 x * ψ0 (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hn : ‖ψ0 x‖ * ‖ψ0 (-x)‖ = 1 := by rw [← norm_mul, hm, norm_one]
  by_contra hne
  have hlt : ‖ψ0 x‖ < 1 := lt_of_le_of_ne h1 hne
  have : ‖ψ0 x‖ * ‖ψ0 (-x)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) hlt
  linarith

def toCircle (ψ0 : AddChar k ℂ) (h : ∀ x, ‖ψ0 x‖ = 1) : AddChar k Circle where
  toFun x := ⟨ψ0 x, mem_sphere_zero_iff_norm.2 (h x)⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (show ψ0 (a + b) = ψ0 a * ψ0 b from AddChar.map_add_eq_mul ψ0 a b)

theorem toCircle_apply (ψ0 : AddChar k ℂ) (h : ∀ x, ‖ψ0 x‖ = 1) (x : k) :
    ((toCircle ψ0 h x : Circle) : ℂ) = ψ0 x := rfl

theorem unitary_and_separates : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    (∀ x, ‖ψ0 x‖ = 1) ∧ ∀ a : k, a ∉ 𝒪[k] → ∃ c : k, (∀ y ∈ 𝒪[k], ψ0 (c * y) = 1) ∧ ψ0 (c * a) ≠ 1 := by
  intro k _ _ _ _ ψ0 hc h1
  have hu := norm_eq_one ψ0 hc
  refine ⟨hu, fun a ha => ?_⟩
  set ψ := toCircle ψ0 hu
  have hψc : Continuous ψ := Continuous.subtype_mk hc _
  have hψ1 : ψ ≠ 1 := by
    intro h
    apply h1
    ext x
    have := congrArg (fun χ : AddChar k Circle => ((χ x : Circle) : ℂ)) h
    simpa [ψ, toCircle_apply] using this
  obtain ⟨c₀, hc₀⟩ := SplitWeil.exists_hasConductor_of_continuous ψ hψc hψ1
  have hx : a ∉ SplitWeil.cball (c₀ * c₀⁻¹) := by
    rw [mul_inv_cancel]
    intro h
    exact ha ((Valuation.mem_integer_iff _ _).mpr (by simpa [SplitWeil.cball] using h))
  obtain ⟨t, ht, hne⟩ := hc₀.exists_ne_one c₀ hx
  refine ⟨t, fun y hy => ?_, fun h => hne (Circle.ext (by simpa [ψ, toCircle_apply] using h))⟩
  have hy' : valuation k y ≤ 1 := hy
  have : t * y ∈ SplitWeil.cball c₀ := by
    simp only [SplitWeil.cball, Set.mem_setOf_eq, map_mul] at ht ⊢
    exact (mul_le_mul' le_rfl hy').trans (by rw [mul_one]; exact ht)
  have := hc₀.eq_one this
  simpa [ψ, toCircle_apply] using congrArg (fun z : Circle => (z : ℂ)) this

end GlobalTheory.CharSep
