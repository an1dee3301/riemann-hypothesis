module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastRowTopComponentDualWeylEqMonomialMul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
public import Formalism.GradedWeylDivisibility.StatementA
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRow_top_component_dualWeyl_eq_monomial_mul : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : Fin n → ℕ) (G : BP K n), G ∈ dualWeyl K (n + 1) n lam → ∀ b : Fin n → ℕ, (∀ s, b s ≤ lam s) → (∀ β', zcomp K n β' G ≠ 0 → omg β' ≤ omg fun s => (b s : ℤ)) → ∃ f ∈ dualWeyl K n n (fun s => lam s - b s), zcomp K n (fun s => (b s : ℤ)) G = zmon K n b * emb K n f := by
  first | exact @GlobalTheory.BrCompare.zcomp_top_eq_zmon_mul_emb | exact GlobalTheory.BrCompare.zcomp_top_eq_zmon_mul_emb | (intros; apply GlobalTheory.BrCompare.zcomp_top_eq_zmon_mul_emb <;> assumption)
