module

public import Mathlib
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.Dynamics.Ergodic.Action.Regular
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.LatticeUnimod

theorem unimodular_of_isFundamentalDomain :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
      (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G),
      IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ →
        μ 𝓕 ≠ 0 ∧ μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ 𝓕 h𝓕 hfin
  have h0 : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have hmap : ∀ g : G, μ.map (· * g) = μ := by
    intro g
    have hc : μ.map (· * g) = Measure.haarScalarFactor (μ.map (· * g)) μ • μ :=
      Measure.isMulLeftInvariant_eq_smul _ _
    have hF : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ :=
      h𝓕.preimage_of_equiv (quasiMeasurePreserving_mul_right μ g) (e := id)
        Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc])
    have hm : μ ((· * g) ⁻¹' 𝓕) = μ 𝓕 := hF.measure_eq h𝓕
    have e1 : (μ.map (· * g)) 𝓕 = μ ((· * g) ⁻¹' 𝓕) :=
      (MeasurableEquiv.mulRight g).map_apply 𝓕
    have e2 : ((Measure.haarScalarFactor (μ.map (· * g)) μ : ℝ≥0) : ℝ≥0∞) * μ 𝓕 = 1 * μ 𝓕 := by
      have e3 := congrArg (fun m : Measure G => m 𝓕) hc
      simp only [Measure.smul_apply] at e3
      rw [e1, hm] at e3
      rw [one_mul]
      exact e3.symm
    have e4 := (ENNReal.mul_left_inj h0 hfin.ne).1 e2
    have e5 : Measure.haarScalarFactor (μ.map (· * g)) μ = 1 := ENNReal.coe_eq_one.1 e4
    rw [e5, one_smul] at hc
    exact hc
  haveI hR : μ.IsMulRightInvariant := ⟨hmap⟩
  refine ⟨h0, hR, ⟨?_⟩⟩
  let c : ℝ≥0∞ := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h2 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul c continuous_inv.measurable.aemeasurable,
      ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h2
  obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : G)
  have hVpos : 0 < μ V := Measure.measure_pos_of_mem_nhds μ hV1
  have e : c ^ 2 * μ V = 1 ^ 2 * μ V := by
    conv_rhs => rw [μeq]
    simp
  have e2 : c ^ 2 = 1 ^ 2 := (ENNReal.mul_left_inj hVpos.ne' hV.measure_lt_top.ne).1 e
  have e3 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective e2
  rw [hc, e3, one_smul]

end GlobalTheory.CompanionTheory.SW.LatticeUnimod
