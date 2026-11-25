module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharComponentTrivialIntegersEventually
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.PsiProd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F]

def intFin (y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) : Af F :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
    (fun v => ⟨(y v).1, (y v).2⟩)

theorem continuous_intFin : Continuous (intFin (F := F)) :=
  RestrictedProduct.isEmbedding_structureMap.continuous

theorem evalV_intFin (y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F))
    (w : HeightOneSpectrum (𝓞 F)) : evalV F w (intFin y) = (y w : Fv F w) := rfl

theorem intFin_nsmul (n : ℕ) (y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) :
    intFin (n • y) = n • intFin y := by
  refine GlobalTheory.AdelicU.af_ext fun w => ?_
  rw [map_nsmul, evalV_intFin, evalV_intFin]
  rfl

theorem exists_finset_trivial (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) :
    ∃ I : Finset (HeightOneSpectrum (𝓞 F)), ∀ y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F),
      (∀ v ∈ I, y v = 0) → ψ (LinearMap.inr F (Ainf F) (Af F) (intFin y)) = 1 := by
  let ι : (∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) → AF F := fun y =>
    LinearMap.inr F (Ainf F) (Af F) (intFin y)
  have hι : Continuous ι := continuous_const.prodMk continuous_intFin
  have hopen : IsOpen {y | ‖ψ (ι y) - 1‖ < 1 / 2} :=
    isOpen_lt ((hψ.comp hι).sub continuous_const).norm continuous_const
  have h0 : (0 : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) ∈ {y | ‖ψ (ι y) - 1‖ < 1 / 2} := by
    have : ι 0 = 0 := by
      have h : intFin (0 : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) = 0 := by
        simpa using intFin_nsmul (F := F) 0 0
      show LinearMap.inr F (Ainf F) (Af F) (intFin 0) = (0 : AF F)
      rw [h, map_zero]
    simp [this, AddChar.map_zero_eq_one]
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hopen 0 h0
  refine ⟨I, fun y hy => GlobalTheory.eq_one_of_forall_norm_pow_sub_one_lt _ fun n => ?_⟩
  have hmem : n • y ∈ (I : Set _).pi u := by
    intro a ha
    have : (n • y) a = 0 := by rw [Pi.smul_apply, hy a ha, smul_zero]
    rw [this]; exact (hu a ha).2
  have e : (ι (n • y) : AF F) = n • (ι y : AF F) := by
    show LinearMap.inr F (Ainf F) (Af F) (intFin (n • y)) = _
    rw [intFin_nsmul, map_nsmul]
  have h := hsub hmem
  simp only [Set.mem_setOf_eq] at h
  rwa [e, AddChar.map_nsmul_eq_pow] at h

end GlobalTheory.PsiProd

namespace GlobalTheory.PsiProd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem addChar_sum {A ι : Type} [AddCommMonoid A] (χ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem psiAt_eq_one_of_integral {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (I : Finset (HeightOneSpectrum (𝓞 F)))
    (hI : ∀ y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F),
      (∀ v ∈ I, y v = 0) → ψ (LinearMap.inr F (Ainf F) (Af F) (intFin y)) = 1)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ I) (a : Fv F v) (ha : a ∈ v.adicCompletionIntegers F) :
    GlobalTheory.LatVac.psiAt ψ v a = 1 := by
  classical
  let y : ∀ u : HeightOneSpectrum (𝓞 F), ↥(u.adicCompletionIntegers F) := Pi.single v ⟨a, ha⟩
  have hy : ∀ u ∈ I, y u = 0 := fun u hu => Pi.single_eq_of_ne (by rintro rfl; exact hv hu) _
  have hfin : intFin y = GlobalTheory.AdelicU.singleFin v a := by
    refine GlobalTheory.AdelicU.af_ext fun w => ?_
    rw [evalV_intFin]
    by_cases e : w = v
    · subst e
      rw [GlobalTheory.AdelicU.evalV_singleFin_self]
      simp [y]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e]
      simp [y, Pi.single_eq_of_ne e]
  have := hI y hy
  rw [hfin] at this
  exact this

theorem psi_prod : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ x : AF F,
    (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evFin F v x)).Finite ∧
    ψ x = ψ (pairA F (fstA F x) 0) * ∏ᶠ v : Pl (F := F), GlobalTheory.LatVac.psiAt ψ v (evFin F v x) := by
  intro F _ _ ψ hψ x
  classical
  obtain ⟨I, hI⟩ := exists_finset_trivial ψ hψ
  set xf : Af F := sndA F x with hxf
  have hT : {v : HeightOneSpectrum (𝓞 F) | evalV F v xf ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 xf.2
  let S : Finset (HeightOneSpectrum (𝓞 F)) := I ∪ hT.toFinset
  have hev : ∀ v, evFin F v x = evalV F v xf := fun v => rfl
  have hsupp : (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evFin F v x)) ⊆ (S : Set _) := by
    intro v hv
    by_contra hvS
    apply hv
    simp only [S, Finset.coe_union, Set.mem_union, Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      not_or, not_not] at hvS
    show GlobalTheory.LatVac.psiAt ψ v (evFin F v x) = 1
    rw [hev]
    exact psiAt_eq_one_of_integral ψ I hI v hvS.1 _ hvS.2
  refine ⟨(S.finite_toSet).subset hsupp, ?_⟩
  let j : Af F →ₗ[F] AF F := LinearMap.inr F (Ainf F) (Af F)
  let χ : AddChar (Af F) ℂ := ψ.compAddMonoidHom j.toAddMonoidHom
  have hχ : ∀ a, χ a = ψ (j a) := fun a => rfl
  have hloc : ∀ v (a : Fv F v), GlobalTheory.LatVac.psiAt ψ v a = χ (GlobalTheory.AdelicU.singleFin v a) := fun v a => rfl
  have hx : x = pairA F (fstA F x) 0 + j xf := by
    refine Prod.ext ?_ ?_
    · show x.1 = x.1 + (0 : Ainf F)
      rw [add_zero]
    · show x.2 = (0 : Af F) + x.2
      rw [zero_add]
  let r : ∀ w : HeightOneSpectrum (𝓞 F), ↥(w.adicCompletionIntegers F) := fun w =>
    if hw : w ∈ S then 0 else ⟨evalV F w xf, by
      have : w ∉ hT.toFinset := fun h => hw (Finset.mem_union_right _ h)
      simpa using this⟩
  have hr : ∀ v ∈ I, r v = 0 := fun v hv => dif_pos (Finset.mem_union_left _ hv)
  have hdec : xf = ∑ v ∈ S, GlobalTheory.AdelicU.singleFin v (evalV F v xf) + intFin r := by
    refine GlobalTheory.AdelicU.af_ext fun w => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, evalV_intFin]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w (fun b _ hb => GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hb) _)
        (fun h => absurd hw h), GlobalTheory.AdelicU.evalV_singleFin_self]
      simp [r, hw]
    · rw [Finset.sum_eq_zero (fun b hb => GlobalTheory.AdelicU.evalV_singleFin_ne (by rintro rfl; exact hw hb) _)]
      simp [r, hw]
  have hrr : χ (intFin r) = 1 := hI r hr
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  conv_lhs => rw [hx]
  rw [AddChar.map_add_eq_mul]
  congr 1
  rw [← hχ, hdec, AddChar.map_add_eq_mul, hrr, mul_one, addChar_sum]
  exact Finset.prod_congr rfl fun v _ => by rw [hloc, hev]

end GlobalTheory.PsiProd
