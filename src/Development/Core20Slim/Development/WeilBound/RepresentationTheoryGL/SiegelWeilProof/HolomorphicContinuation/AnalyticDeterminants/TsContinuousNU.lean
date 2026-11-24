module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Classical
public import Init.Core
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem ts_inG_mul {g h : M2 n} (hg : InG g) (hh : InG h) : InG (g * h) := by
  unfold InG at *
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * JJ n * (g * h) = hᴴ * (gᴴ * JJ n * g) * h := by simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [hg, hh]

theorem ts_herm_conjTranspose (x : Fin n → Fin n → ℝ) : (herm x)ᴴ = herm x := by
  ext i j
  rw [conjTranspose_apply]
  apply Complex.ext <;> simp [herm] <;> ring

theorem ts_inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (nU b) := by
  unfold InG nU JJ
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hb]

theorem ts_continuous_herm : Continuous (herm : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℂ) := by
  unfold herm
  fun_prop

theorem ts_continuous_nU : Continuous (nU : Matrix (Fin n) (Fin n) ℂ → M2 n) := by
  unfold nU
  exact Continuous.matrix_fromBlocks continuous_const continuous_id continuous_const continuous_const

set_option maxHeartbeats 1000000 in
theorem twoSided : TwoSided := by
  intro n H F Γ hF hΓ hcl hperm ψ hψc hψs hvan h a b ha hb
  have : FirstCountableTopology (M2 n) :=
    inferInstanceAs (FirstCountableTopology (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))
  obtain ⟨γ, hγΓ, hγa⟩ := mem_closure_iff_seq_limit.1 (hcl ha)
  have hmap : Continuous (fun p : M2 n × (Fin n → Fin n → ℝ) => p.1 * nU (herm p.2) * b) :=
    (continuous_fst.mul (ts_continuous_nU.comp (ts_continuous_herm.comp continuous_snd))).mul continuous_const
  have hmem : ∀ c x, InG c → InG (c * nU (herm x) * b) := fun c x hc =>
    ts_inG_mul (ts_inG_mul hc (ts_inG_nU (ts_herm_conjTranspose x))) hb
  have hΦc : ∀ c, InG c → Continuous (fun x => F h (c * nU (herm x) * b)) := by
    intro c hc
    have hcx : Continuous (fun x : Fin n → Fin n → ℝ => c * nU (herm x) * b) :=
      (continuous_const.mul (ts_continuous_nU.comp ts_continuous_herm)).mul continuous_const
    exact (hF h).comp_continuous hcx fun x => hmem c x hc
  have hzero : ∀ k, ∫ x, F h (γ k * nU (herm x) * b) * ψ x = 0 := by
    intro k
    obtain ⟨h', hh'⟩ := hperm (γ k) (hγΓ k) h
    have e : ∀ x, F h (γ k * nU (herm x) * b) * ψ x = F h' (nU (herm x) * b) * ψ x := by
      intro x
      rw [Matrix.mul_assoc, hh' _ (ts_inG_mul (ts_inG_nU (ts_herm_conjTranspose x)) hb)]
    simp_rw [e]
    exact hvan h' b hb
  have hS : IsCompact (insert a (Set.range γ)) := hγa.isCompact_insert_range
  have hSG : insert a (Set.range γ) ⊆ {g | InG g} := by
    rintro c (rfl | ⟨k, rfl⟩)
    · exact ha
    · exact hΓ _ (hγΓ k)
  have hC : IsCompact ((fun p : M2 n × (Fin n → Fin n → ℝ) => p.1 * nU (herm p.2) * b) ''
      (insert a (Set.range γ) ×ˢ tsupport ψ)) := (hS.prod hψs).image hmap
  have hCG : (fun p : M2 n × (Fin n → Fin n → ℝ) => p.1 * nU (herm p.2) * b) ''
      (insert a (Set.range γ) ×ˢ tsupport ψ) ⊆ {g | InG g} := by
    rintro _ ⟨⟨c, x⟩, ⟨hc, -⟩, rfl⟩
    exact hmem c x (hSG hc)
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn ((hF h).mono hCG)
  have hbound : ∀ c ∈ insert a (Set.range γ), ∀ x, ‖F h (c * nU (herm x) * b) * ψ x‖ ≤ M * ‖ψ x‖ := by
    intro c hc x
    rw [norm_mul]
    by_cases hx : x ∈ tsupport ψ
    · exact mul_le_mul_of_nonneg_right (hM _ ⟨⟨c, x⟩, ⟨hc, hx⟩, rfl⟩) (norm_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  have hlim : Tendsto (fun k => ∫ x, F h (γ k * nU (herm x) * b) * ψ x) atTop
      (𝓝 (∫ x, F h (a * nU (herm x) * b) * ψ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => M * ‖ψ x‖) (fun k => ?_) ?_ (fun k => ?_) ?_
    · exact ((hΦc _ (hΓ _ (hγΓ k))).mul hψc).aestronglyMeasurable
    · exact (hψc.norm.integrable_of_hasCompactSupport hψs.norm).const_mul M
    · exact Eventually.of_forall fun x => hbound _ (Set.mem_insert_of_mem _ ⟨k, rfl⟩) x
    · refine Eventually.of_forall fun x => ?_
      refine Tendsto.mul_const _ ?_
      have hw : ContinuousWithinAt (F h) {g | InG g} (a * nU (herm x) * b) := hF h _ (hmem a x ha)
      refine hw.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => hmem _ x (hΓ _ (hγΓ k))⟩)
      exact ((hγa.mul tendsto_const_nhds).mul tendsto_const_nhds)
  have h0 : Tendsto (fun k => ∫ x, F h (γ k * nU (herm x) * b) * ψ x) atTop (𝓝 0) := by
    simp_rw [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim h0

end PositivityTheory.Rg.Sw.LVs
