module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacter
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.Annihilator

variable {F : Type} [Field F] [NumberField F]

private theorem ext_lemma {x y : AF F} (h1 : fstA F x = fstA F y) (h2 : sndA F x = sndA F y) :
    x = y :=
  Prod.ext h1 h2

private theorem mul_pairA_zero (x : AF F) (z : Ainf F) :
    x * pairA F z 0 = pairA F (fstA F x * z) 0 := by
  apply ext_lemma
  · rw [map_mul]
    rfl
  · rw [map_mul]
    show sndA F x * 0 = 0
    exact mul_zero _

private theorem mul_pairA_singleV (x : AF F) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    x * pairA F 0 (singleV F v t) = pairA F 0 (singleV F v (sndA F x v * t)) := by
  apply ext_lemma
  · rw [map_mul]
    show fstA F x * 0 = 0
    exact mul_zero _
  · rw [map_mul]
    show sndA F x * singleV F v t = singleV F v (sndA F x v * t)
    unfold singleV
    classical
    exact (RestrictedProduct.mul_single _ v t (sndA F x)).symm

theorem eq_zero_of_forall [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (x : AF F)
    (hx : ∀ y, ψ (x * y) = 1) : x = 0 := by
  obtain ⟨hloc, -, hinf⟩ := GlobalTheory.GaugeEx.CharLoc.char_local F ψ hψ
  apply ext_lemma
  ·
    have h0 : fstA F x = 0 := hinf _ fun y => by
      have h := hx (pairA F y 0)
      rw [mul_pairA_zero] at h
      exact h
    rw [h0, map_zero]
  ·
    have key : ∀ v, sndA F x v = 0 := by
      intro v
      by_contra hne
      obtain ⟨s, hs⟩ := hloc v
      apply hs
      have h := hx (pairA F 0 (singleV F v ((sndA F x v)⁻¹ * s)))
      rw [mul_pairA_singleV, mul_inv_cancel_left₀ hne] at h
      exact h
    rw [map_zero]
    exact DFunLike.ext _ _ fun v => (key v).trans rfl

theorem exists_eq_of_forall [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (x : AF F)
    (hx : ∀ ξ : F, ψ (x * algebraMap F (AF F) ξ) = 1) : ∃ ξ : F, x = algebraMap F (AF F) ξ := by
  by_cases htriv : ∀ y, ψ (x * y) = 1
  · exact ⟨0, by rw [map_zero]; exact eq_zero_of_forall hψ x htriv⟩
  · push_neg at htriv
    obtain ⟨hc, hn, -, -⟩ := id hψ

    have hχ : IsCharAF F (ψ.compAddMonoidHom (AddMonoidHom.mulLeft x)) := by
      unfold IsCharAF
      exact ⟨hc.comp (continuous_const.mul continuous_id), fun y => hn _, hx, htriv⟩
    obtain ⟨a, -, ha⟩ := GlobalTheory.AdeleCharTwist.exists_mul_eq F ψ _ hψ hχ
    refine ⟨a, sub_eq_zero.mp (eq_zero_of_forall hψ _ fun y => ?_)⟩
    have h1 : ψ (x * y) = ψ (algebraMap F (AF F) a * y) := ha y
    rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, h1, ← AddChar.map_add_eq_mul,
      add_neg_cancel, AddChar.map_zero_eq_one]

theorem self_annihilator : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → (∀ x : AF F, (∀ y, ψ (x * y) = 1) → x = 0) ∧ ∀ x : AF F, (∀ ξ : F, ψ (x * algebraMap F (AF F) ξ) = 1) → ∃ ξ : F, x = algebraMap F (AF F) ξ := by
  intro F _ _ hF ψ hψ
  haveI := hF
  exact ⟨fun x hx => eq_zero_of_forall hψ x hx, fun x hx => exists_eq_of_forall hψ x hx⟩

end GlobalTheory.SWQ.Annihilator
