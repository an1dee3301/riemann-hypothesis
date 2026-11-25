module

public import Mathlib
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.IdempotentMatrixMonoidHom.prM :
    {R A : Type} →
      [inst : CommRing R] →
        [inst_1 : CommRing A] →
          [Algebra R A] →
            (e : R) → e * e = e → (ι : Type) → [inst : Fintype ι] → [inst_3 : DecidableEq ι] → Matrix ι ι A →* Matrix ι ι A :=
  fun {R A} _ _ _ e he ι _ _ =>
    { toFun := fun M => e • M + (1 - e) • (1 : Matrix ι ι A)
      map_one' := by rw [← add_smul, add_sub_cancel, one_smul]
      map_mul' := fun M N => by
        have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
        have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
        have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, h2, sub_zero]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
          smul_smul, he, h1, h2, h3, zero_smul, add_zero, zero_add, Matrix.mul_one] }
