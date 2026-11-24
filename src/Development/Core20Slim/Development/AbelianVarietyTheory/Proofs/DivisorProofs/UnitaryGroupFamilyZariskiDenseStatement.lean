module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupFamilyZariskiDense
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGNeZero
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

open Classical MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_family_zariski_dense : ∀ {ι : Type} [Fintype ι] {a : ℕ} (Q : MvPolynomial (ι × Fin a × Fin a) ℂ), (∀ g : ι → Matrix.unitaryGroup (Fin a) ℂ, MvPolynomial.eval (fun v : ι × Fin a × Fin a => (g v.1 : Matrix (Fin a) (Fin a) ℂ) v.2.1 v.2.2) Q = 0) → Q = 0 := by
  first | exact @GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense | exact GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense | (intros; apply GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense <;> assumption)
