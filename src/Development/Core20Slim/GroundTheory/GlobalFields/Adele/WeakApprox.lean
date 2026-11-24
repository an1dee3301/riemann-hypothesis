module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Function.Defs
public import Mathlib.Logic.Pairwise
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField

variable {K : Type*} [Field K] [NumberField K]

section AbsoluteValues

theorem adicAbv_lt_one_iff_mem (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    NumberField.HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K x) < 1 ↔ x ∈ v.asIdeal := by
  rw [← FinitePlace.norm_embedding]
  exact FinitePlace.norm_lt_one_iff_mem K v x

theorem adicAbv_isNontrivial (v : HeightOneSpectrum (𝓞 K)) : (NumberField.HeightOneSpectrum.adicAbv K v).IsNontrivial := by
  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
  · simpa using hx0
  · exact ((adicAbv_lt_one_iff_mem v x).2 hxv).ne

theorem not_isEquiv_adicAbv {v v' : HeightOneSpectrum (𝓞 K)} (h : v ≠ v') :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv (NumberField.HeightOneSpectrum.adicAbv K v') := by
  intro he
  have hle : ¬ v.asIdeal ≤ v'.asIdeal := fun hle ↦
    h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle))
  obtain ⟨x, hxv, hxv'⟩ := Set.not_subset.1 hle
  have h1 := (adicAbv_lt_one_iff_mem v x).2 hxv
  rw [he.lt_one_iff] at h1
  exact hxv' ((adicAbv_lt_one_iff_mem v' x).1 h1)

theorem not_isEquiv_adicAbv_infinitePlace (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K) :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv w.1 := by
  intro he
  have h1 : NumberField.HeightOneSpectrum.adicAbv K v (2 : K) ≤ 1 := by
    simpa using NumberField.HeightOneSpectrum.adicAbv_natCast_le_one K v 2
  rw [he.le_one_iff] at h1
  have h2 : w.1 (2 : K) = 2 := by
    have h := w.map_natCast 2
    rw [Nat.cast_ofNat, Nat.cast_ofNat] at h
    exact h
  linarith

end AbsoluteValues

section Density

variable (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))

noncomputable def placeAbv : S ⊕ T → AbsoluteValue K ℝ :=
  Sum.elim (fun v ↦ NumberField.HeightOneSpectrum.adicAbv K v.1) (fun w ↦ w.1.1)

theorem placeAbv_isNontrivial : ∀ i, (placeAbv S T i).IsNontrivial
  | .inl v => adicAbv_isNontrivial v.1
  | .inr w => w.1.isNontrivial

theorem placeAbv_pairwise_not_isEquiv :
    Pairwise fun i j ↦ ¬ (placeAbv S T i).IsEquiv (placeAbv S T j) := by
  rintro (⟨v, hv⟩ | ⟨w, hw⟩) (⟨v', hv'⟩ | ⟨w', hw'⟩) hij he
  · exact not_isEquiv_adicAbv (fun h ↦ hij (by subst h; rfl)) he
  · exact not_isEquiv_adicAbv_infinitePlace v w' he
  · exact not_isEquiv_adicAbv_infinitePlace v' w he.symm
  · exact hij (by
      have : w = w' := InfinitePlace.eq_iff_isEquiv.2 he
      subst this; rfl)

theorem isometry_algebraMap_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    Isometry ((algebraMap K (v.adicCompletion K)).comp
      (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v)).toRingHom) := by
  refine AddMonoidHomClass.isometry_of_norm _ fun x ↦ ?_
  rw [WithAbs.norm_eq_apply_ofAbs, ← FinitePlace.norm_embedding]
  rfl

theorem denseRange_algebraMap_prod_pi :
    DenseRange (fun x : K ↦ ((fun v : S ↦ algebraMap K (v.1.adicCompletion K) x),
      (fun w : T ↦ algebraMap K w.1.Completion x))) := by
  classical
  let φ : ∀ v : S, WithAbs (placeAbv S T (.inl v)) → v.1.adicCompletion K := fun v ↦
    (algebraMap K (v.1.adicCompletion K)).comp
      (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1)).toRingHom
  let ψ : ∀ w : T, WithAbs (placeAbv S T (.inr w)) → w.1.Completion := fun w y ↦
    ((show WithAbs w.1.1 from y) : w.1.Completion)
  have hφc : ∀ v, Continuous (φ v) := fun v ↦ (isometry_algebraMap_adicCompletion v.1).continuous
  have hφd : ∀ v, DenseRange (φ v) := by
    intro v
    have h := HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) (K := K) v.1
    unfold DenseRange at h ⊢
    convert h using 1
    show Set.range (⇑(algebraMap K (v.1.adicCompletion K)) ∘
      ⇑(WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1))) = _
    exact (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1)).surjective.range_comp _
  have hψc : ∀ w, Continuous (ψ w) := fun w ↦ InfinitePlace.Completion.continuous_coe w.1
  have hψd : ∀ w, DenseRange (ψ w) := fun w ↦ InfinitePlace.Completion.denseRange_coe w.1
  let e := Homeomorph.sumPiEquivProdPi S T (fun i ↦ WithAbs (placeAbv S T i))
  have hc : Continuous (Prod.map (Pi.map φ) (Pi.map ψ) ∘ e) :=
    ((continuous_pi fun v ↦ (hφc v).comp (continuous_apply v)).prodMap
      (continuous_pi fun w ↦ (hψc w).comp (continuous_apply w))).comp e.continuous
  have hg : DenseRange (Prod.map (Pi.map φ) (Pi.map ψ) ∘ e) :=
    ((DenseRange.piMap hφd).prodMap (DenseRange.piMap hψd)).comp e.surjective.denseRange
      ((continuous_pi fun v ↦ (hφc v).comp (continuous_apply v)).prodMap
        (continuous_pi fun w ↦ (hψc w).comp (continuous_apply w)))
  have hd := AbsoluteValue.denseRange_algebraMap_pi (placeAbv_isNontrivial S T)
    (placeAbv_pairwise_not_isEquiv S T)
  convert hg.comp hd hc using 1
  funext x
  simp [φ, ψ, e, Function.comp_apply, Homeomorph.sumPiEquivProdPi]
  constructor
  · funext v
    simp [Pi.map, WithAbs.equiv, placeAbv]
    rfl
  · funext w
    simp [Pi.map, placeAbv]
    exact AbsoluteValue.Completion.algebraMap_def (R := K) (v := w.1.1) x

end Density

end GroundTheory.Global
