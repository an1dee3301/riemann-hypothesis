module

public import Mathlib
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.SuccPred.Nat

@[expose] public section

noncomputable section

namespace GlobalTheory.StdLoc

def rowBlockIndicatorFrom (a : ℕ) {d : ℕ} (i : Fin d) : ℕ := if a ≤ i.1 then 1 else 0

def blockPar (R : Type) [CommRing R] (a d : ℕ) : Subgroup (GL (Fin d) R) where
  carrier := {g | (g : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)}
  mul_mem' := fun {x y} hx hy => by
    show ((x * y : GL (Fin d) R) : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)
    rw [Units.val_mul]; exact hx.mul hy
  one_mem' := by
    show ((1 : GL (Fin d) R) : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)
    rw [Units.val_one]; exact Matrix.blockTriangular_one
  inv_mem' := fun {x} hx => by
    show ((x⁻¹ : GL (Fin d) R) : Matrix (Fin d) (Fin d) R).BlockTriangular (rowBlockIndicatorFrom a)
    letI : Invertible (x : Matrix (Fin d) (Fin d) R) := Units.invertible x
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hx

theorem _root_.GlobalTheory.StdLoc.mem_blockPar {R : Type} [CommRing R] {a d : ℕ} (g : GL (Fin d) R) :
    g ∈ _root_.GlobalTheory.StdLoc.blockPar R a d ↔ ∀ i j : Fin d, j.1 < a → a ≤ i.1 → (g : Matrix (Fin d) (Fin d) R) i j = 0 := by
  show (g : Matrix (Fin d) (Fin d) R).BlockTriangular (_root_.GlobalTheory.StdLoc.rowBlockIndicatorFrom a) ↔ _
  unfold Matrix.BlockTriangular _root_.GlobalTheory.StdLoc.rowBlockIndicatorFrom
  constructor
  · intro h i j hj hi
    apply h
    simp [hi, not_le.mpr hj]
  · intro h i j hlt
    refine h i j ?_ ?_ <;> split_ifs at hlt <;> omega

def glVol (q : ℝ) (n : ℕ) : ℝ := ∏ i ∈ Finset.Icc 1 n, (1 - (q ^ i)⁻¹)

def blockIdx (q : ℝ) (c a a' : ℕ) : ℝ := q ^ (c * a * a') * glVol q (a + a') / (glVol q a * glVol q a')

end GlobalTheory.StdLoc
