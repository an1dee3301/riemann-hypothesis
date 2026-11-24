module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsActionOnRowWeight
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Formalism.GradedWeylDivisibility.StatementA
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight : ∀ (R : Type) [CommRing R] (r n : ℕ) (μ : Fin r → ℕ) (f : MvPolynomial (Fin r × Fin n) R), IsWeightedHomogeneous (rowW r n) f μ → (∀ a, rowE R r n a a f = (μ a : R) • f) ∧ ∀ a b, a ≠ b → (μ b = 0 → rowE R r n a b f = 0) ∧ ∀ μ' : Fin r → ℕ, μ' + Pi.single b 1 = μ + Pi.single a 1 → IsWeightedHomogeneous (rowW r n) (rowE R r n a b f) μ' := by
  first | exact @GlobalTheory.Alc.rowE_rowWeight | exact GlobalTheory.Alc.rowE_rowWeight | (intros; apply GlobalTheory.Alc.rowE_rowWeight <;> assumption)
