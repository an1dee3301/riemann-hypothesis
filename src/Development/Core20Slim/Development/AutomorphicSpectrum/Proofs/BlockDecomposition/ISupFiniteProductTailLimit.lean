module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TprodComplementSplitFinset
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.EulerFactorStandardMeasureIdentity
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Subtype
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open Filter Topology

namespace GlobalTheory.CompanionTheory.TailProd

theorem term_mono {ι : Type} [DecidableEq ι] (Mv τ p : ι → ℝ) (S : Finset ι)
    (hτ : Summable (fun v => |τ v - 1|)) (hp : Summable (fun v => |p v - 1|))
    (hM0 : ∀ v, 0 ≤ Mv v) (hτ0 : ∀ v, 0 ≤ τ v) (hp0 : ∀ v, 0 ≤ p v)
    (hle : ∀ v, v ∉ S → τ v * p v ≤ Mv v) :
    Monotone (fun S' : Finset ι => (∏ v ∈ (S ∪ S') \ S, Mv v) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) := by
  intro S₁ S₂ h12
  have hU : S ∪ S₁ ⊆ S ∪ S₂ := Finset.union_subset_union_right h12
  dsimp only
  rw [GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι τ (S ∪ S₁) (S ∪ S₂) hτ hU,
    GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι p (S ∪ S₁) (S ∪ S₂) hp hU]
  have hX : ∏ v ∈ (S ∪ S₂) \ S, Mv v =
      (∏ v ∈ (S ∪ S₁) \ S, Mv v) * ∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), Mv v := by
    have hD : ((S ∪ S₂) \ S) \ ((S ∪ S₁) \ S) = (S ∪ S₂) \ (S ∪ S₁) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [← Finset.prod_sdiff (Finset.sdiff_subset_sdiff hU (Finset.Subset.refl S)), hD, mul_comm]
  have hΔ : (∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), τ v) * (∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), p v) ≤
      ∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), Mv v := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun v _ => mul_nonneg (hτ0 v) (hp0 v))
      (fun v hv => hle v (fun hvS => (Finset.mem_sdiff.1 hv).2 (Finset.mem_union_left _ hvS)))
  have hX1 : 0 ≤ ∏ v ∈ (S ∪ S₁) \ S, Mv v := Finset.prod_nonneg fun v _ => hM0 v
  have hT : 0 ≤ ∏' v : {v // v ∉ S ∪ S₂}, τ v.1 :=
    (GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {v // v ∉ S ∪ S₂} (fun v => τ v.1)
      (hτ.comp_injective Subtype.val_injective)).2.2.2 fun v => hτ0 v.1
  have hP : 0 ≤ ∏' v : {v // v ∉ S ∪ S₂}, p v.1 :=
    (GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {v // v ∉ S ∪ S₂} (fun v => p v.1)
      (hp.comp_injective Subtype.val_injective)).2.2.2 fun v => hp0 v.1
  rw [hX]
  set X := ∏ v ∈ (S ∪ S₁) \ S, Mv v
  set D := (S ∪ S₂) \ (S ∪ S₁)
  set T := ∏' v : {v // v ∉ S ∪ S₂}, τ v.1
  set P := ∏' v : {v // v ∉ S ∪ S₂}, p v.1
  calc X * ((∏ v ∈ D, τ v) * T * ((∏ v ∈ D, p v) * P))
      = X * ((∏ v ∈ D, τ v) * (∏ v ∈ D, p v)) * (T * P) := by ring
    _ ≤ X * (∏ v ∈ D, Mv v) * (T * P) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΔ hX1) (mul_nonneg hT hP)

theorem iSup_partial_mul_tails : ∀ (ι : Type) [DecidableEq ι] (Mv τ p : ι → ℝ) (S : Finset ι),
    Summable (fun v => |Mv v - 1|) → Summable (fun v => |τ v - 1|) → Summable (fun v => |p v - 1|) →
    (∀ v, 0 ≤ Mv v) → (∀ v, 0 ≤ τ v) → (∀ v, 0 ≤ p v) → (∀ v, v ∉ S → τ v * p v ≤ Mv v) →
    ⨆ S' : Finset ι, ENNReal.ofReal ((∏ v ∈ (S ∪ S') \ S, Mv v) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) =
      ENNReal.ofReal (∏' v : {v // v ∉ S}, Mv v.1) := by
  intro ι _ Mv τ p S hMs hτs hps hM0 hτ0 hp0 hle
  have hmono := GlobalTheory.CompanionTheory.TailProd.term_mono Mv τ p S hτs hps hM0 hτ0 hp0 hle
  have hg : Tendsto (fun S' : Finset ι => S ∪ S') atTop atTop :=
    tendsto_atTop_mono (fun S' => (Finset.subset_union_right : S' ⊆ S ∪ S')) tendsto_id
  have hM := (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one Mv hMs).comp hg
  have hT := (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one τ hτs).comp hg
  have hP := (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one p hps).comp hg
  have hlim : Tendsto (fun S' : Finset ι => (∏' v : {v // v ∉ S}, Mv v.1) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * (∏' v : {v // v ∉ S ∪ S'}, p v.1) /
        ∏' v : {v // v ∉ S ∪ S'}, Mv v.1)) atTop (𝓝 (∏' v : {v // v ∉ S}, Mv v.1)) := by
    have := (tendsto_const_nhds (x := ∏' v : {v // v ∉ S}, Mv v.1)).mul
      ((hT.mul hP).div hM one_ne_zero)
    simpa only [Function.comp_def, Pi.div_apply, mul_one, div_one] using this
  have hA : Tendsto (fun S' : Finset ι => (∏ v ∈ (S ∪ S') \ S, Mv v) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) atTop
      (𝓝 (∏' v : {v // v ∉ S}, Mv v.1)) := by
    refine hlim.congr' ?_
    filter_upwards [hM.eventually_ne one_ne_zero] with S' hS'
    dsimp only [Function.comp] at hS' ⊢
    rw [GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι Mv S (S ∪ S') hMs Finset.subset_union_left,
      mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hS']
  exact iSup_eq_of_tendsto (fun a b h => ENNReal.ofReal_le_ofReal (hmono h))
    ((ENNReal.continuous_ofReal.tendsto _).comp hA)

end GlobalTheory.CompanionTheory.TailProd
