module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.MeasurableSetUH
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsEqAdelicCharMul
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinUnfoldingIdentity
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsEqAdelicCharMul
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evalV_apply (v : HeightOneSpectrum (𝓞 F)) (a : Af F) : evalV F v a = a v := rfl

open Classical in
theorem evalV_singleV_same (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : evalV F v (singleV F v y) = y := by
  rw [evalV_apply]
  unfold singleV
  exact RestrictedProduct.single_eq_same _ _ _

open Classical in
theorem evalV_singleV_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (y : Fv F v) : evalV F w (singleV F v y) = 0 := by
  rw [evalV_apply]
  unfold singleV
  exact RestrictedProduct.single_eq_of_ne _ _ h

theorem addChar_sum {A M ι : Type} [AddCommMonoid A] [CommMonoid M] (ψ : AddChar A M) (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem AF_ext {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : sndA F a = sndA F b) : a = b :=
  Prod.ext (α := Ainf F) (β := Af F) h1 h2

theorem fstA_pairA (x : Ainf F) (y : Af F) : fstA F (pairA F x y) = x := rfl

theorem sndA_pairA (x : Ainf F) (y : Af F) : sndA F (pairA F x y) = y := rfl

theorem psi_split (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ x : AF F,
      (∀ v, v ∉ S → evalV F v (sndA F x) ∈ v.adicCompletionIntegers F) →
      ψ x = psiInf F ψ (fstA F x) * ∏ v ∈ S, psiV F ψ v (evalV F v (sndA F x)) := by
  classical
  obtain ⟨ξ, hξ⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ algebraMap F (Fv F v) ξ ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 (GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.ev_rat ξ)
  refine ⟨hfin.toFinset, fun S hS x hx => ?_⟩
  set xf : Af F := sndA F x with hxf
  set r : Af F := xf - ∑ v ∈ S, singleV F v (evalV F v xf) with hr
  have hdec : x = pairA F (fstA F x) 0 + ∑ v ∈ S, pairA F 0 (singleV F v (evalV F v xf)) + pairA F 0 r := by
    refine AF_ext ?_ ?_
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_add (f := _), map_add (f := _), map_sum, fstA_pairA, fstA_pairA]
        simp only [fstA_pairA, Finset.sum_const_zero, add_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_add (f := _), map_add (f := _), map_sum, sndA_pairA, sndA_pairA]
        simp only [sndA_pairA, hr, hxf]
        abel
  have hrv : ∀ v, evalV F v r = if v ∈ S then 0 else evalV F v xf := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hr, map_sub, map_sum]
    by_cases hv : v ∈ S
    · rw [if_pos hv, Finset.sum_eq_single v]
      · rw [evalV_singleV_same, sub_self]
      · intro w _ hw
        exact evalV_singleV_ne (Ne.symm hw) _
      · intro h; exact absurd hv h
    · rw [if_neg hv, Finset.sum_eq_zero, sub_zero]
      intro w hw
      exact evalV_singleV_ne (by rintro rfl; exact hv hw) _
  have hmem : algebraMap F (Af F) ξ * r ∈ GroundTheory.Global.finiteInvDifferent F := by
    intro v
    have e1 : (algebraMap F (Af F) ξ * r) v = algebraMap F (Fv F v) ξ * evalV F v r := rfl
    rw [e1, hrv v]
    by_cases hv : v ∈ S
    · rw [if_pos hv, mul_zero]
      exact zero_mem _
    · rw [if_neg hv]
      have hξv : algebraMap F (Fv F v) ξ ∈ v.adicCompletionIntegers F := by
        by_contra h
        exact hv (hS (hfin.mem_toFinset.2 h))
      exact GroundTheory.Global.mem_localInvDifferent_of_mem (mul_mem hξv (hx v hv))
  have hr1 : ψ (pairA F 0 r) = 1 := by
    rw [hξ]
    have e2 : algebraMap F (AF F) ξ * pairA F 0 r = pairA F 0 (algebraMap F (Af F) ξ * r) := by
      refine AF_ext ?_ ?_
      · rw [map_mul, fstA_pairA, fstA_pairA, mul_zero]
      · rw [map_mul, sndA_pairA, sndA_pairA, AlgHom.commutes]
    rw [e2]
    have hm2 : pairA F 0 (algebraMap F (Af F) ξ * r) ∈ GroundTheory.Global.invDifferentAdeles F :=
      GroundTheory.Global.mem_invDifferentAdeles.mpr hmem
    rw [GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles hm2]
    simp [pairA]
  have h1 : ψ x = ψ (pairA F (fstA F x) 0 + ∑ v ∈ S, pairA F 0 (singleV F v (evalV F v xf)) + pairA F 0 r) :=
    congrArg ψ hdec
  rw [h1, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, addChar_sum, hr1, mul_one]
  rfl

end PositivityTheory.SiegelWeilFormula.GFac

end
