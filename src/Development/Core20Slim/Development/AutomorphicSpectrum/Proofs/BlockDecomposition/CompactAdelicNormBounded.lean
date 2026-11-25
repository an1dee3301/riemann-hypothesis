module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroMemBoxF
public import Development.Core20Slim.GroundTheory.AutomorphicForms.ReductionFinite
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.Core20Slim.GroundTheory.AutomorphicForms.ReductionHeight
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Operations
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Lattice
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
open IsDedekindDomain

noncomputable section

namespace GlobalTheory.CompanionTheory.RedCov.Simple.NormBound

open GroundTheory.Automorphic.Reduction

theorem finprod_le_prod_of_le {α : Type*} {f b : α → ℝ} (S : Finset α) (h0 : ∀ a, 0 ≤ f a)
    (hS : ∀ a ∈ S, f a ≤ b a) (hb : ∀ a ∈ S, 1 ≤ b a) (h1 : ∀ a, a ∉ S → f a ≤ 1) :
    ∏ᶠ a, f a ≤ ∏ a ∈ S, b a := by
  classical
  have hone : (1 : ℝ) ≤ ∏ a ∈ S, b a := by
    have := Finset.prod_le_prod₀ (s := S) (f := fun _ => (1 : ℝ)) (g := b)
      (fun _ _ => zero_le_one) hb
    simpa using this
  by_cases hf : (Function.mulSupport f).Finite
  · set c : α → ℝ := fun a => if a ∈ S then b a else 1 with hc
    have hcs : Function.mulSupport c ⊆ (S : Set α) := fun a ha => by
      by_contra h
      exact ha (by simp only [hc]; exact if_neg fun h' => h (Finset.mem_coe.2 h'))
    have hcf : (Function.mulSupport c).Finite := S.finite_toSet.subset hcs
    have hle : ∏ᶠ a, f a ≤ ∏ᶠ a, c a :=
      finprod_le_finprod_of_nonneg hf hcf h0 fun a => by
        simp only [hc]
        split_ifs with h
        · exact hS a h
        · exact h1 a h
    rw [finprod_eq_prod_of_mulSupport_subset c hcs] at hle
    refine hle.trans (le_of_eq (Finset.prod_congr rfl fun a ha => ?_))
    simp only [hc]
    rw [if_pos ha]
  · rw [finprod_of_infinite_mulSupport hf]
    exact hone

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

def integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (Fin N → AF F) :=
  {y | ∀ i, ∀ v, v ∉ S → (y i).2 v ∈ v.adicCompletionIntegers F}

theorem isOpen_integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (integralOutside (N := N) S) := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ∉ S)
  have h2 : IsOpen {a : AF F | ∀ v, v ∉ S → a.2 v ∈ v.adicCompletionIntegers F} :=
    h.preimage continuous_snd
  have : integralOutside (N := N) S = ⋂ i : Fin N, (fun y : Fin N → AF F => y i) ⁻¹'
      {a : AF F | ∀ v, v ∉ S → a.2 v ∈ v.adicCompletionIntegers F} := by
    ext y
    simp only [integralOutside, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact isOpen_iInter_of_finite fun i => h2.preimage (continuous_apply i)

theorem exists_mem_integralOutside (y : Fin N → AF F) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), y ∈ integralOutside S := by
  have h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i, (y i).2 v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (y i).2.2
  have hfin := Filter.eventually_cofinite.1 h
  refine ⟨hfin.toFinset, fun i v hv => ?_⟩
  by_contra hc
  exact hv (hfin.mem_toFinset.2 fun h' => hc (h' i))

theorem exists_finset_subset_integralOutside {D : Set (Fin N → AF F)} (hD : IsCompact D) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), D ⊆ integralOutside S := by
  classical
  obtain ⟨T, hT⟩ := hD.elim_finite_subcover
    (fun S : Finset (HeightOneSpectrum (𝓞 F)) => integralOutside (N := N) S)
    isOpen_integralOutside (fun y _ => by
      obtain ⟨S, hS⟩ := exists_mem_integralOutside y
      exact Set.mem_iUnion.2 ⟨S, hS⟩)
  refine ⟨T.sup id, fun y hy i v hv => ?_⟩
  obtain ⟨S, hS, hyS⟩ := Set.mem_iUnion₂.1 (hT hy)
  exact hyS i v fun h => hv (Finset.mem_sup.2 ⟨S, hS, h⟩)

theorem norm_finComp_le_one {y : Fin N → AF F} {v : HeightOneSpectrum (𝓞 F)}
    (h : ∀ i, (y i).2 v ∈ v.adicCompletionIntegers F) : ‖finComp v y‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i =>
    (Valued.toNormedField.norm_le_one_iff).2
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h i))

theorem continuous_euclidNorm_infComp (w : InfinitePlace F) :
    Continuous fun y : Fin N → AF F => euclidNorm (infComp w y) :=
  continuous_euclidNorm.comp (continuous_pi fun i =>
    (continuous_apply w).comp (continuous_fst.comp (continuous_apply i)))

theorem continuous_norm_finComp (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun y : Fin N → AF F => ‖finComp v y‖ :=
  (continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp
    (continuous_snd.comp (continuous_apply i))).norm

end GlobalTheory.CompanionTheory.RedCov.Simple.NormBound

namespace GlobalTheory.CompanionTheory.RedCov.Simple


open GroundTheory.Automorphic.Reduction NormBound in
theorem exists_adelicNorm_le_of_isCompact :
    ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (D : Set (Fin N → AF F)), IsCompact D →
      ∃ P : ℝ, 0 < P ∧ ∀ y ∈ D, GroundTheory.Automorphic.Reduction.adelicNorm y ≤ P := by
  intro F _ _ N D hD
  classical
  obtain ⟨S, hS⟩ := exists_finset_subset_integralOutside hD
  choose a ha1 ha using fun w : InfinitePlace F =>
    exists_one_le_bound hD (continuous_euclidNorm_infComp (N := N) w)
  choose b hb1 hb using fun v : HeightOneSpectrum (𝓞 F) =>
    exists_one_le_bound hD (continuous_norm_finComp (N := N) v)
  have hA : (1 : ℝ) ≤ ∏ w, a w ^ w.mult := by
    have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : InfinitePlace F => (1 : ℝ))
      (g := fun w => a w ^ w.mult) (fun _ _ => zero_le_one)
      (fun w _ => one_le_pow₀ (ha1 w))
    simpa using this
  have hB : (1 : ℝ) ≤ ∏ v ∈ S, b v := by
    have := Finset.prod_le_prod₀ (s := S) (f := fun _ => (1 : ℝ)) (g := b)
      (fun _ _ => zero_le_one) (fun v _ => hb1 v)
    simpa using this
  refine ⟨(∏ w, a w ^ w.mult) * ∏ v ∈ S, b v, by positivity, fun y hy => ?_⟩
  refine mul_le_mul ?_ ?_ (finprod_nonneg fun _ => norm_nonneg _) (by positivity)
  · exact Finset.prod_le_prod₀ (fun w _ => pow_nonneg (euclidNorm_nonneg _) _)
      fun w _ => pow_le_pow_left₀ (euclidNorm_nonneg _) (ha w y hy) _
  · exact finprod_le_prod_of_le S (fun _ => norm_nonneg _) (fun v _ => hb v y hy)
      (fun v _ => hb1 v) fun v hv => norm_finComp_le_one fun i => hS hy i v hv

end GlobalTheory.CompanionTheory.RedCov.Simple

end
