module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.Push

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EvNonzero

theorem pure_ne_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ) (hf : f ≠ 0)
    (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ≠ 0 := by
  classical
  obtain ⟨yi, hyi⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  have hS : Set.Finite {v | ¬ (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)} :=
    Filter.eventually_cofinite.mp hstd
  choose p hp using fun v => Function.ne_iff.mp (h0 v)
  set S := hS.toFinset with hSdef
  let yf : κ → FiniteAdeleRing (𝓞 F) F := fun i =>
    (⟨fun v => if v ∈ S then p v i else 0, by
      apply Filter.eventually_cofinite.mpr
      refine S.finite_toSet.subset ?_
      intro v hv
      by_contra hvS
      apply hv
      have hvS' : v ∉ S := fun h => hvS (Finset.mem_coe.mpr h)
      show (if v ∈ S then p v i else 0) ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      rw [if_neg hvS']
      exact zero_mem (v.adicCompletionIntegers F)⟩ :
      RestrictedProduct (fun v : Pl F => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)
  let x : κ → AdeleRing (𝓞 F) F := fun i =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (yi i), yf i) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  intro hz
  have hx := congrFun hz x
  have h1 : (fun i => evI F (x i)) = yi := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (yi i)) = yi i
    exact RingEquiv.apply_symm_apply _ _
  have h2 : ∀ v, (fun i => evFin F v (x i)) = fun i => if v ∈ S then p v i else 0 := fun v => rfl
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.zero_apply, h1, h2] at hx
  have hg : ∀ v, v ∉ S → φ v (fun i => if v ∈ S then p v i else 0) = 1 := by
    intro v hv
    have hv' : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      by_contra h
      exact hv (hS.mem_toFinset.mpr h)
    rw [hv']
    have hzero : (fun i : κ => if v ∈ S then p v i else 0) = fun _ => 0 := funext fun i => if_neg hv
    rw [hzero, Set.indicator_of_mem (show (fun _ : κ => (0 : Fv F v)) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun i => zero_mem _)]
    rfl
  have hsub : Function.mulSupport (fun v => φ v (fun i => if v ∈ S then p v i else 0)) ⊆ S := by
    intro v hv
    by_contra h
    exact hv (hg v h)
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub] at hx
  refine (mul_ne_zero hyi (Finset.prod_ne_zero_iff.mpr fun v hv => ?_)) hx
  have hpv : (fun i : κ => if v ∈ S then p v i else 0) = p v := funext fun i => if_pos hv
  rw [hpv]
  exact hp v


end GlobalTheory.EvNonzero

end
