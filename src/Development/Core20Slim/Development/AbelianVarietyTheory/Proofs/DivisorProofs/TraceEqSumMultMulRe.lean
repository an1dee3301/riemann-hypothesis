module

public import Mathlib
public import Batteries.Classes.RatCast
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Perfect
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

namespace GlobalTheory.TraceRealEmbeddingSum

open NumberField

theorem re_embedding_mk {F : Type} [Field F] (φ : F →+* ℂ) (x : F) :
    ((InfinitePlace.mk φ).embedding x).re = (φ x).re := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h <;>
    simp [h, ComplexEmbedding.conjugate_coe_eq]

theorem trace_eq_sum_mult_mul_re {F : Type} [Field F] [NumberField F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) =
      ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re := by
  classical

  have htr : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ σ : F →ₐ[ℚ] ℂ, σ x := by
    rw [← trace_eq_sum_embeddings ℂ (K := ℚ) (L := F), eq_ratCast]
  have hre : ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, (φ x).re := by
    have h := congrArg Complex.re htr
    rw [Complex.ratCast_re, Complex.re_sum] at h
    rw [h, ← (RingHom.equivRatAlgHom F ℂ).sum_comp]
    rfl

  rw [hre, ← Finset.univ.sum_fiberwise (fun φ : F →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hfib : ∀ φ ∈ Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w),
      (φ x).re = (w.embedding x).re := by
    intro φ hφ
    rw [(Finset.mem_filter.mp hφ).2.symm, re_embedding_mk]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    nsmul_eq_mul]

end GlobalTheory.TraceRealEmbeddingSum
