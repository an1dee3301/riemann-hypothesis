module

public import Mathlib
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace GlobalTheory.CompanionTheory.MatrixRowSpace

variable {K : Type} [Field K]

theorem row_mul {m n r : ℕ} (x : Matrix (Fin m) (Fin r) K) (c : Matrix (Fin r) (Fin n) K)
    (i : Fin m) : (x * c) i = c.vecMulLinear (x i) := by
  ext j
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

theorem range_vecMulLinear_eq {n r : ℕ} (c : Matrix (Fin r) (Fin n) K) :
    LinearMap.range c.vecMulLinear = Submodule.span K (Set.range c) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [Matrix.vecMulLinear_apply, Matrix.vecMul_eq_sum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    ext j
    simp [Matrix.vecMul, dotProduct, Pi.single_apply]

theorem span_rows_mul {m n r : ℕ} (x : Matrix (Fin m) (Fin r) K) (c : Matrix (Fin r) (Fin n) K) :
    Submodule.span K (Set.range (x * c)) =
      (Submodule.span K (Set.range x)).map c.vecMulLinear := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [row_mul]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, ← row_mul]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem span_rows_eq_top_iff {m r : ℕ} (x : Matrix (Fin m) (Fin r) K) :
    x.rank = r ↔ Submodule.span K (Set.range x) = ⊤ := by
  rw [Matrix.rank_eq_finrank_span_row]
  constructor
  · intro h
    exact Submodule.eq_top_of_finrank_eq (h.trans (by simp))
  · intro h
    have h' : Submodule.span K (Set.range x.row) = ⊤ := h
    rw [h', finrank_top]
    simp

theorem span_rows_mul_of_rank {m n r : ℕ} (x : Matrix (Fin m) (Fin r) K)
    (c : Matrix (Fin r) (Fin n) K) (hx : x.rank = r) :
    Submodule.span K (Set.range (x * c)) = Submodule.span K (Set.range c) := by
  rw [span_rows_mul, (span_rows_eq_top_iff x).mp hx, Submodule.map_top, range_vecMulLinear_eq]

end GlobalTheory.CompanionTheory.MatrixRowSpace
