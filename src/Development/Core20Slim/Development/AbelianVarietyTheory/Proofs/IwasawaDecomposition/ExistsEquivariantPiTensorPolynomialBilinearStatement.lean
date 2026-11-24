module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantPiTensorPolynomialBilinear
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.Core20Slim.ReciprocityTheory.DualLattices.FischerSelfNeZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_piTensor_polynomialBilinear : ∀ (ι : Type) [Fintype ι] (N n : ℕ) (A B : ι → Type) [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (I : ∀ i, MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i), (∀ i, I i ≠ 0) → ∃ It : MvPolynomial (ι × Fin N × Fin n) ℂ →ₗ[ℂ] (⨂[ℂ] i, A i) →ₗ[ℂ] ⨂[ℂ] i, B i, It ≠ 0 ∧ ∀ (c : ι → ℂ) (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (a : ∀ i, A i →ₗ[ℂ] A i) (b : ∀ i, B i →ₗ[ℂ] B i), (∀ i P v, I i (c i • subst2 (h i) (g i) P) (a i v) = b i (I i P v)) → ∀ P x, It ((∏ i, c i) • substF h g P) (PiTensorProduct.map a x) = PiTensorProduct.map b (It P x) := by
  first | exact @GlobalTheory.CompactHowe.PolyTensor.exists_tensor | exact GlobalTheory.CompactHowe.PolyTensor.exists_tensor | (intros; apply GlobalTheory.CompactHowe.PolyTensor.exists_tensor <;> assumption)
