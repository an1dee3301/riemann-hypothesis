module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffCoefficientSpaceActionMemRange
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReprMemOfCoeff
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.L2.DIV MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_coefficientSpaceAction_mem_range : ∀ {ι : Type} [Fintype ι] {n : ℕ} {E : Type} [Field E] (emb : ι → E →+* ℂ) {L : Type} [Field L] (κ : L →+* ℂ), (∀ (τ : ι) (x : E), emb τ x ∈ Set.range κ) → ∀ (lam : ι → Formalism.BasicNotions.DomWeight n) (g : GL (Fin n) E) (v : VV ℂ lam), (∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ) → ∀ m, AddMonoidAlgebra.coeff ((rhoVr emb lam g) v).1 m ∈ Set.range κ := by
  first | exact @GlobalTheory.RowRho.coeff_rhoVr_mem_range | exact GlobalTheory.RowRho.coeff_rhoVr_mem_range | (intros; apply GlobalTheory.RowRho.coeff_rhoVr_mem_range <;> assumption)
