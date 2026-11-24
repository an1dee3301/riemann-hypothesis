module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationMemOfIsGLSchemeSubmodule
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowPolarization_mem_of_isGLSchemeSubmodule : ∀ (k : Type) [Field k] (N : ℕ) (lam : DomWeight N) (M : Submodule k (MvPolynomial (Fin N × Fin N) k)), GlobalTheory.Published.IsGLSubmodule k N lam M → ∀ a b : Fin N, a ≠ b → ∀ f ∈ M, rowE k N N a b f ∈ M := by
  first | exact @GlobalTheory.Alc.rowE_mem_of_isGLSubmodule | exact GlobalTheory.Alc.rowE_mem_of_isGLSubmodule | (intros; apply GlobalTheory.Alc.rowE_mem_of_isGLSubmodule <;> assumption)
