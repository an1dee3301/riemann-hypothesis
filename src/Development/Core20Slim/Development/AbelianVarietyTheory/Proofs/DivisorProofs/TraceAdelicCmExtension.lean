module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Push

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK 

noncomputable section

namespace GlobalTheory.CMTrace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sig_ne_id {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hr : w.IsReal := by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    simp only [ComplexEmbedding.conjugate_coe_eq]
    have := h.2.2.2 w.embedding x
    rw [hc x] at this
    exact this.symm
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr (h.2.1.isComplex w)) hr

def sigE {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : Gal(E/F) :=
  AlgEquiv.ofAlgHom σ σ (AlgHom.ext fun x => sig_sig h x) (AlgHom.ext fun x => sig_sig h x)

theorem trace_eq {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (e : E) :
    algebraMap F E (Algebra.trace F E e) = e + σ e := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1
  have hne : (1 : Gal(E/F)) ≠ sigE h := by
    intro h1
    obtain ⟨x, hx⟩ := sig_ne_id h
    exact hx (congrArg (fun g : Gal(E/F) => g x) h1).symm
  have hle : Nat.card Gal(E/F) ≤ 2 := by
    calc Nat.card Gal(E/F) ≤ Nat.card (E →ₐ[F] E) :=
          Nat.card_le_card_of_injective (fun g => (g : E →ₐ[F] E)) (fun a b hab => AlgEquiv.coe_algHom_injective hab)
      _ ≤ Module.finrank F E := card_algHom_le_finrank F E E
      _ = 2 := h.2.2.1
  have hall : ∀ g : Gal(E/F), g = 1 ∨ g = sigE h := by
    classical
    have hc : (({1, sigE h} : Finset Gal(E/F))).card = 2 := Finset.card_pair hne
    have hu : ({1, sigE h} : Finset Gal(E/F)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hc]
      rw [← Nat.card_eq_fintype_card]
      have : 2 ≤ Nat.card Gal(E/F) := by
        rw [Nat.card_eq_fintype_card, ← hc]; exact Finset.card_le_univ _
      omega
    intro g
    have := Finset.mem_univ g
    rw [← hu] at this
    simpa using this
  have hgal : IsGalois F E := by
    apply IsGalois.of_card_aut_eq_finrank
    rw [h.2.2.1]
    apply le_antisymm hle
    classical
    rw [Nat.card_eq_fintype_card, ← Finset.card_pair hne]
    exact Finset.card_le_univ _
  rw [trace_eq_sum_automorphisms]
  classical
  rw [Fintype.sum_eq_add 1 (sigE h) hne (fun g hg => absurd (hall g) (by tauto))]
  rfl

end GlobalTheory.CMTrace

namespace GlobalTheory.CMTrace


end GlobalTheory.CMTrace
