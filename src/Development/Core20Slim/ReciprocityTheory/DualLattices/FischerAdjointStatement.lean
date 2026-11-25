module

public import Mathlib
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

noncomputable section

open MvPolynomial Matrix Finset

namespace ReciprocityTheory.PGsh

section Cayley

variable (n : ℕ) (R : Type*) [CommRing R]





end Cayley

section Tests

variable (R : Type*) [CommRing R]

end Tests

section HW

variable {ν : ℕ} {ι : Type*}

def rowSubst (g : Matrix (Fin ν) (Fin ν) ℂ) :
    MvPolynomial (Fin ν × ι) ℂ →ₐ[ℂ] MvPolynomial (Fin ν × ι) ℂ :=
  aeval fun p => ∑ l, C (g l p.1) * X (l, p.2)


open scoped Classical in
def fischer (P Q : MvPolynomial (Fin ν × ι) ℂ) : ℂ := by
  classical
  exact ∑ A ∈ P.support ∪ Q.support,
    AddMonoidAlgebra.coeff P A * starRingEnd ℂ (AddMonoidAlgebra.coeff Q A) * ((A.prod fun _ e => e.factorial : ℕ) : ℂ)

def IsUpperUnitri (g : Matrix (Fin ν) (Fin ν) ℂ) : Prop :=
  (∀ i, g i i = 1) ∧ ∀ i j, j < i → g i j = 0

end HW

end ReciprocityTheory.PGsh
