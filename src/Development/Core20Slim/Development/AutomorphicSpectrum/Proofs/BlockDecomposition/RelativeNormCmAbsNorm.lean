module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

@[expose] public section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig

theorem norm_eq_mul_conj_and_absNorm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ t : 𝓞 E, algebraMap F E ((RingOfIntegers.norm F t : 𝓞 F) : F) = (t : E) * σ (t : E) ∧ Ideal.absNorm (Ideal.span {RingOfIntegers.norm F t}) = Ideal.absNorm (Ideal.span {t}) := by
  intro F E _ _ _ _ _ σ hσ t
  classical
  obtain ⟨_, hE, hdeg, hconj⟩ := hσ
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hdeg]; norm_num)
  refine ⟨?_, ?_⟩
  · set σ' : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (AlgHom.bijective σ) with hσ'
    have hne : σ' ≠ 1 := by
      intro h
      have hx : ∀ x, σ x = x := fun x => by
        have := congrArg (fun g : E ≃ₐ[F] E => g x) h
        simpa [hσ'] using this
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
      have hwc : w.IsComplex := hE.isComplex w
      rw [InfinitePlace.isComplex_iff] at hwc
      apply hwc
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply, ← hconj, hx]
    have hcard_le : Fintype.card (E ≃ₐ[F] E) ≤ 2 := by
      rw [← hdeg]
      exact (Fintype.card_le_of_injective (fun g : E ≃ₐ[F] E => (g : E →ₐ[F] E))
        (fun a b h => AlgEquiv.ext fun x => DFunLike.congr_fun h x)).trans AlgHom.card_le
    have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, σ'} := by
      symm
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_univ, Finset.card_pair hne.symm]
      exact hcard_le
    haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by
      rw [hdeg, Nat.card_eq_fintype_card]
      apply le_antisymm hcard_le
      rw [← Finset.card_univ, huniv, Finset.card_pair hne.symm])
    change algebraMap F E (Algebra.norm F (t : E)) = _
    rw [Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hne.symm]
    simp [hσ']
  · rw [Ideal.absNorm_span_singleton, Ideal.absNorm_span_singleton]
    congr 1
    apply Int.cast_injective (α := ℚ)
    rw [Algebra.coe_norm_int, Algebra.coe_norm_int]
    change Algebra.norm ℚ (Algebra.norm F (t : E)) = Algebra.norm ℚ (t : E)
    rw [Algebra.norm_norm]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig
