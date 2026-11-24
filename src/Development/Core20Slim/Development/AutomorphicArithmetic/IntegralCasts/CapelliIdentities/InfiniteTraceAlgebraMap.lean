module

public import Mathlib
public import Batteries.Classes.RatCast
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Data.Zero
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
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.WithAbs
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
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Perfect
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

theorem UpperTheory.Reformulated.B.Qh34.aux1.{u_1} :
    ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K],
      ∑ x : NumberField.InfinitePlace K,
          (↑x.mult : ℝ) *
            ((NumberField.InfinitePlace.Completion.extensionEmbedding x : x.Completion → ℂ)
                ((0 : NumberField.InfiniteAdeleRing K) x)).re =
        (0 : ℝ) := by
  intro K _ _
  refine Finset.sum_eq_zero fun w _ => ?_
  have h : (0 : NumberField.InfiniteAdeleRing K) w = 0 := rfl
  rw [h, map_zero, Complex.zero_re, mul_zero]

theorem UpperTheory.Reformulated.B.Qh34.aux2.{u_1} :
    ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (x y : NumberField.InfiniteAdeleRing K),
      ∑ w : NumberField.InfinitePlace K,
          (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) ((x + y) w)).re =
        ∑ w : NumberField.InfinitePlace K,
            (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (x w)).re +
          ∑ w : NumberField.InfinitePlace K,
            (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (y w)).re := by
  intro K _ _ x y
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : (x + y) w = x w + y w := rfl
  rw [h, map_add (f := _), Complex.add_re, mul_add]

noncomputable def UpperTheory.Reformulated.B.Qh34.infiniteTrace.{u_1} :
    (K : Type u_1) → [inst : Field K] → [NumberField K] → NumberField.InfiniteAdeleRing K →+ ℝ :=
    fun (K : Type u_1) [Field K] [NumberField K] ↦
      {
        toFun := fun (x : NumberField.InfiniteAdeleRing K) ↦
          ∑ w : NumberField.InfinitePlace K,
            (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (x w)).re,
        map_zero' := UpperTheory.Reformulated.B.Qh34.aux1 K, map_add' := UpperTheory.Reformulated.B.Qh34.aux2 K : NumberField.InfiniteAdeleRing K →+ ℝ }

theorem UpperTheory.Reformulated.B.Qh34.infiniteTrace_algebraMap.{u_1} :
    ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (k : K),
      (UpperTheory.Reformulated.B.Qh34.infiniteTrace K : NumberField.InfiniteAdeleRing K → ℝ)
          ((Algebra.algebraMap K (NumberField.InfiniteAdeleRing K) : K → NumberField.InfiniteAdeleRing K) k) =
        (↑((Algebra.trace ℚ K : K → ℚ) k) : ℝ) := by
  classical
  intro K _ _ k
  have h1 : ((Algebra.trace ℚ K k : ℚ) : ℝ) = ∑ φ : K →+* ℂ, (φ k).re := by
    have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := k)
    have h' : ∑ φ : K →+* ℂ, φ k = ∑ σ : K →ₐ[ℚ] ℂ, σ k :=
      Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun _ => rfl)
    rw [← Complex.re_sum, h', ← h]
    simp
  rw [h1, ← Finset.sum_fiberwise Finset.univ NumberField.InfinitePlace.mk]
  change ∑ w : NumberField.InfinitePlace K, (↑w.mult : ℝ) *
    (NumberField.InfinitePlace.Completion.extensionEmbedding w
      (algebraMap K (NumberField.InfiniteAdeleRing K) k w)).re = _
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 : NumberField.InfinitePlace.Completion.extensionEmbedding w
      (algebraMap K (NumberField.InfiniteAdeleRing K) k w) = w.embedding k := by
    simp
  have h3 : ∀ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => NumberField.InfinitePlace.mk φ = w),
      (φ k).re = (w.embedding k).re := by
    intro φ hφ
    rw [← (Finset.mem_filter.1 hφ).2]
    rcases NumberField.InfinitePlace.embedding_mk_eq φ with h | h
    · rw [h]
    · rw [h, NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  rw [h2, Finset.sum_congr rfl h3, Finset.sum_const, NumberField.InfinitePlace.card_filter_mk_eq,
    nsmul_eq_mul]
