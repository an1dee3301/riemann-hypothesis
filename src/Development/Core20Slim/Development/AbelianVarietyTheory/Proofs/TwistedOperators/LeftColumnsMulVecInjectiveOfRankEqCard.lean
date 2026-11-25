module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
public import Init.ByCases
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Module.Torsion.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Embedding
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory


open Matrix Topology Module in
theorem _root_.GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card :
    ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → (∀ i j, x i (e (Sum.inr j)) = 0) → ∀ v : a → k, (x.submatrix id (fun i => e (Sum.inl i))) *ᵥ v = 0 → v = 0 := by
  intro k m a b n _ _ _ _ _ e x hx hz v hv
  classical
  set x' := x.submatrix id (fun i => e (Sum.inl i))
  let Q : Matrix n a k := Matrix.of fun l i => if l = e (Sum.inl i) then 1 else 0
  let P : Matrix a n k := Matrix.of fun i l => if l = e (Sum.inl i) then 1 else 0
  have hQ : x' = x * Q := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [x', Q, Matrix.of_apply, Matrix.submatrix_apply, id, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hP : x = x' * P := by
    ext i l
    obtain ⟨t, rfl⟩ := e.surjective l
    rcases t with t | t
    · rw [Matrix.mul_apply]
      simp only [x', P, Matrix.of_apply, Matrix.submatrix_apply, id, mul_ite, mul_one, mul_zero,
        EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    · rw [Matrix.mul_apply]
      simp [x', P, hz]
  have hr : x'.rank = Fintype.card a := by
    apply le_antisymm
    · rw [← hx, hQ]; exact Matrix.rank_mul_le_left _ _
    · rw [← hx, hP]; exact Matrix.rank_mul_le_left _ _
  have hrn := LinearMap.finrank_range_add_finrank_ker x'.mulVecLin
  have hxr : finrank k (LinearMap.range x'.mulVecLin) = Fintype.card a := hr
  rw [hxr, finrank_fintype_fun_eq_card] at hrn
  have hker : LinearMap.ker x'.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
  have hvk : v ∈ LinearMap.ker x'.mulVecLin := hv
  rw [hker] at hvk
  exact (Submodule.mem_bot k).1 hvk

end GlobalTheory
