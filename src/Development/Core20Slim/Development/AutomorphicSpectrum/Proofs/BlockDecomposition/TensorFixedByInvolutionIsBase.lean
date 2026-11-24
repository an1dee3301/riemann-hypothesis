module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin

theorem sigR_fixed_eq_algebraMap : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (a : K ⊗[F] E),
    sigR K σ a = a → ∃ x : K, algebraMap K (K ⊗[F] E) x = a := by
  intro F E _ _ _ _ _ σ h K _ _ a ha
  have hsigma (x : E) : σ (σ x) = x := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hmoved : ∃ y, σ y ≠ y := by
    by_contra hc
    push_neg at hc
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hreal : ComplexEmbedding.IsReal τ := ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
      rw [ComplexEmbedding.conjugate_coe_eq]
      have := h.2.2.2 τ x
      rw [hc x] at this
      exact this.symm)
    have hcx := h.2.1.isComplex (InfinitePlace.mk τ)
    exact (InfinitePlace.isComplex_mk_iff.1 hcx) hreal
  have hex : ∃ (θ : E) (d : F) (B : Module.Basis (Fin 2) F E),
      θ ≠ 0 ∧ d ≠ 0 ∧ σ θ = -θ ∧ θ * θ = algebraMap F E d ∧
      B 0 = 1 ∧ B 1 = θ := by
    obtain ⟨y, hy⟩ := hmoved
    have hE2 : (2 : E) ≠ 0 := two_ne_zero
    have hσθ : σ (y - σ y) = -(y - σ y) := by
      rw [map_sub, hsigma]
      ring
    have hθ : y - σ y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
    generalize y - σ y = θ at hσθ hθ
    have hli : LinearIndependent F ![(1 : E), θ] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      simp only [Algebra.smul_def, mul_one] at hst
      have h1 := congrArg σ hst
      simp only [map_add (f := _), map_mul, AlgHom.commutes, hσθ, map_zero] at h1
      have hs : (2 : E) * algebraMap F E s = 0 := by
        linear_combination hst + h1
      have ht : (2 : E) * (algebraMap F E t * θ) = 0 := by
        linear_combination hst - h1
      have hs0 : s = 0 := by
        have := (mul_eq_zero.1 hs).resolve_left hE2
        exact (map_eq_zero _).1 this
      have ht0 : t = 0 := by
        have := ((mul_eq_zero.1 ((mul_eq_zero.1 ht).resolve_left hE2))).resolve_right hθ
        exact (map_eq_zero _).1 this
      exact ⟨hs0, ht0⟩
    let B : Module.Basis (Fin 2) F E :=
      basisOfLinearIndependentOfCardEqFinrank hli (by rw [h.2.2.1, Fintype.card_fin])
    have hB0 : B 0 = 1 := by simp [B]
    have hB1 : B 1 = θ := by simp [B]
    have hsum := B.sum_repr (θ * θ)
    rw [Fin.sum_univ_two, hB0, hB1] at hsum
    generalize B.repr (θ * θ) 0 = a at hsum
    generalize B.repr (θ * θ) 1 = b at hsum
    have hsum' : algebraMap F E a + algebraMap F E b * θ = θ * θ := by
      simpa only [Algebra.smul_def, mul_one] using hsum
    have hconj := congrArg σ hsum'
    simp only [map_add (f := _), map_mul, AlgHom.commutes, hσθ] at hconj
    have hb : (2 : E) * (algebraMap F E b * θ) = 0 := by
      linear_combination hsum' - hconj
    have hb0 : algebraMap F E b = 0 :=
      (mul_eq_zero.1 ((mul_eq_zero.1 hb).resolve_left hE2)).resolve_right hθ
    have hsq : θ * θ = algebraMap F E a := by
      rw [← hsum', hb0, zero_mul, add_zero]
    have ha : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at hsq
      exact hθ (mul_self_eq_zero.1 hsq)
    exact ⟨θ, a, B, hθ, ha, hσθ, hsq, hB0, hB1⟩
  obtain ⟨θ, d, B, hθ, hd, hσθ, hsq, hB0, hB1⟩ := hex
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let C : Module.Basis (Fin 2) K (K ⊗[F] E) := Algebra.TensorProduct.basis K B
  have hC0 : C 0 = 1 := by
    simp only [C, Algebra.TensorProduct.basis_apply, hB0]
    rfl
  have hC1 : C 1 = (1 : K) ⊗ₜ[F] θ := by
    simp only [C, Algebra.TensorProduct.basis_apply, hB1]
  have hsK : ∀ x : K, sigR K σ (algebraMap K (K ⊗[F] E) x) = algebraMap K (K ⊗[F] E) x := by
    intro x
    change Algebra.TensorProduct.map (AlgHom.id F K) σ (algebraMap K (K ⊗[F] E) x) = _
    simp [Algebra.TensorProduct.algebraMap_apply]
  have hsT : sigR K σ ((1 : K) ⊗ₜ[F] θ) = -((1 : K) ⊗ₜ[F] θ) := by
    change Algebra.TensorProduct.map (AlgHom.id F K) σ ((1 : K) ⊗ₜ[F] θ) = _
    rw [Algebra.TensorProduct.map_tmul, hσθ, TensorProduct.tmul_neg]
    rfl
  have hz := C.sum_repr a
  rw [Fin.sum_univ_two, hC0, hC1, Algebra.smul_def, Algebra.smul_def, mul_one] at hz
  generalize C.repr a 0 = x at hz
  generalize C.repr a 1 = y at hz
  subst hz
  rw [map_add (f := _), map_mul, hsK, hsK, hsT] at ha
  have h2 : algebraMap K (K ⊗[F] E) 0 + algebraMap K (K ⊗[F] E) (2 * y) * ((1 : K) ⊗ₜ[F] θ) = 0 := by
    rw [map_zero, map_mul, map_ofNat]
    linear_combination -ha
  have hl := Fintype.linearIndependent_iff.1 C.linearIndependent ![0, 2 * y] (by
    rw [Fin.sum_univ_two, hC0, hC1]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one] using h2)
  have hy : y = 0 := by
    have := hl 1
    simp only [Matrix.cons_val_one] at this
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  exact ⟨x, by rw [hy, map_zero, zero_mul, add_zero]⟩

end GlobalTheory.CompanionTheory.KFin

end
