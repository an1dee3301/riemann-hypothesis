module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.Infinite
public import Development.Core20Slim.GroundTheory.GlobalFields.KummerTheory.Splitting
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.IsEmpty.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
public import Mathlib.NumberTheory.NumberField.Completion.Ramification
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

@[expose] public section

noncomputable section

namespace GroundTheory.Global

open NumberField Module
open scoped NumberField.LiesOver TensorProduct

namespace InfinitePlace

variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]

def SplitsCompletely (v : NumberField.InfinitePlace K) : Prop :=
  ∀ w : NumberField.InfinitePlace L, w.LiesOver v → w.IsUnramified K

variable {L} (v : NumberField.InfinitePlace K)

theorem isUnramified_iff_finrank_eq_one (w : NumberField.InfinitePlace L) [w.LiesOver v] :
    w.IsUnramified K ↔ finrank v.Completion w.Completion = 1 := by
  refine ⟨fun h ↦ h.finrank_eq_one v, fun h ↦ ?_⟩
  rcases w.isUnramified_or_isRamified K with hu | hr
  · exact hu
  · exact absurd (h.symm.trans (hr.finrank_eq_two v)) (by norm_num)

theorem splitsCompletely_iff_forall_finrank :
    SplitsCompletely L v ↔
      ∀ w : v.placesOver L, finrank v.Completion (w : NumberField.InfinitePlace L).Completion = 1 :=
  ⟨fun h w ↦ (isUnramified_iff_finrank_eq_one v w.1).1 (h w.1 w.2),
    fun h w hw ↦ have := hw; (isUnramified_iff_finrank_eq_one v w).2 (h ⟨w, hw⟩)⟩

variable [NumberField K] [NumberField L]


variable (L) in
theorem nonempty_placesOver : Nonempty (v.placesOver L) := by
  classical
  by_contra h
  rw [not_nonempty_iff] at h
  have := sum_finrank_completion (L := L) v
  rw [Finset.univ_eq_empty, Finset.sum_empty] at this
  exact (Module.finrank_pos (R := K) (M := L)).ne this

end InfinitePlace

end GroundTheory.Global
