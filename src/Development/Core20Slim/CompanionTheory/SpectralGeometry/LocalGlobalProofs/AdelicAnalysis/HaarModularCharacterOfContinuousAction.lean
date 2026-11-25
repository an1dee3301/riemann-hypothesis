module

public import Mathlib
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SProd
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Bornology.Real
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW


open scoped Pointwise in
theorem exists_continuous_modulus_of_continuous_action :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
      [IsTopologicalAddGroup V] (μ : Measure V) [μ.IsAddHaarMeasure] (Q : Type) [Group Q]
      [TopologicalSpace Q] [IsTopologicalGroup Q] [DistribMulAction Q V] [ContinuousSMul Q V],
      ∃ χ : Q →* ℝ≥0, Continuous χ ∧ ∀ q : Q, μ.map (fun v => q • v) = χ q • μ := by
  intro V _ _ _ _ _ _ _ _ μ _ Q _ _ _ _ _
  letI : SMul Q (Set V) := Set.smulSet

  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : V)
  have hKint : (interior K).Nonempty := ⟨0, mem_interior_iff_mem_nhds.2 hK0⟩
  have hKtop : μ K ≠ ∞ := hK.measure_lt_top.ne
  have hKpos : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK0).ne'
  have : μ.Regular := Measure.regular_of_isAddLeftInvariant hK hKint hKtop
  set Δ : Q →* ℝ≥0 := distribHaarChar V with hΔ
  have hmul : ∀ (g : Q) (s : Set V), (Δ g : ℝ≥0∞) * μ s = μ (g • s) := fun g s =>
    distribHaarChar_mul μ g s

  have hup : ∀ b : ℝ≥0, 1 < b → ∀ᶠ q in 𝓝 (1 : Q), Δ q < b := by
    intro b hb
    have hb' : (1 : ℝ≥0∞) < b := by exact_mod_cast hb
    have hlt : μ K < (b : ℝ≥0∞) * μ K := by
      calc μ K = 1 * μ K := (one_mul _).symm
        _ < b * μ K := (ENNReal.mul_lt_mul_iff_left hKpos hKtop).2 hb'
    obtain ⟨O, hKO, hO, hOμ⟩ := Set.exists_isOpen_lt_of_lt K _ hlt
    have hN : IsOpen {p : Q × V | p.1 • p.2 ∈ O} := hO.preimage continuous_smul
    obtain ⟨u, v, hu, -, h1u, hKv, huv⟩ :=
      generalized_tube_lemma (isCompact_singleton : IsCompact ({1} : Set Q)) hK hN (by
        rintro ⟨q, k⟩ ⟨hq, hk⟩
        simp only [Set.mem_singleton_iff] at hq
        subst hq
        simpa using hKO hk)
    filter_upwards [hu.mem_nhds (h1u (Set.mem_singleton 1))] with q hq
    have hsub : q • K ⊆ O := by
      rintro _ ⟨k, hk, rfl⟩
      exact huv (Set.mk_mem_prod hq (hKv hk))
    have h2 : (Δ q : ℝ≥0∞) * μ K < b * μ K := by
      rw [hmul]
      exact (measure_mono hsub).trans_lt hOμ
    exact_mod_cast (ENNReal.mul_lt_mul_iff_left hKpos hKtop).1 h2
  have hcont1 : ContinuousAt Δ 1 := by
    rw [ContinuousAt, map_one]
    refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => hup b hb⟩
    rcases eq_or_ne a 0 with rfl | ha0
    · exact Filter.Eventually.of_forall fun q => distribHaarChar_pos
    · have hb : 1 < a⁻¹ := (one_lt_inv₀ (pos_iff_ne_zero.2 ha0)).2 ha
      have ht : Filter.Tendsto (fun q : Q => q⁻¹) (𝓝 1) (𝓝 1) := by
        simpa using (continuous_inv.tendsto (1 : Q))
      filter_upwards [ht.eventually (hup _ hb)] with q hq
      rw [map_inv] at hq
      exact (inv_lt_inv₀ distribHaarChar_pos (pos_iff_ne_zero.2 ha0)).1 hq
  have hcont : Continuous Δ := continuous_of_continuousAt_one Δ hcont1
  refine ⟨⟨⟨fun q => Δ q⁻¹, by simp⟩, fun a b => by
    simp only [_root_.mul_inv_rev]
    rw [map_mul, mul_comm]⟩, hcont.comp continuous_inv, fun q => ?_⟩
  ext s hs
  rw [Measure.map_apply (continuous_const_smul q).measurable hs]
  show _ = ((Δ q⁻¹ : ℝ≥0) • μ) s
  rw [smul_apply, ENNReal.smul_def, smul_eq_mul, Set.preimage_smul]
  exact (hmul q⁻¹ s).symm

end GlobalTheory.CompanionTheory.SW
