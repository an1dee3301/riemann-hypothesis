module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.DelSqIrreducibleUnitary
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delSq_unitary_stable_and_irreducible : ∀ (n : ℕ) (lam : DomWeight n), FiniteDimensional ℂ (delSq ℂ n lam) ∧ delSq ℂ n lam = nablaSq ℂ n lam ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ), ∀ p ∈ delSq ℂ n lam, Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ delSq ℂ n lam) ∧ ∀ U : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ), U ≤ delSq ℂ n lam → (∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ p ∈ U, Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ U) → U = ⊥ ∨ U = delSq ℂ n lam := by
  first | exact @GlobalTheory.WeylUnitary.delSq_irreducible_unitary | exact GlobalTheory.WeylUnitary.delSq_irreducible_unitary | (intros; apply GlobalTheory.WeylUnitary.delSq_irreducible_unitary <;> assumption)
