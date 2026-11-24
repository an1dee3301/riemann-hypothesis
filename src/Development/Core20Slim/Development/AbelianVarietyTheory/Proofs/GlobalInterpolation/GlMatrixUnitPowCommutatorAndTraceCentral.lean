module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CommPowEntry
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem glRel_pow_comm : ∀ (A : Type) [Ring A] (N : ℕ) (E : Matrix (Fin N) (Fin N) A), GlRel E → ∀ k : ℕ, (∀ a b c d, E a b * (E ^ k) c d - (E ^ k) c d * E a b = (if b = c then (E ^ k) a d else 0) - (if d = a then (E ^ k) c b else 0)) ∧ ∀ a b, E a b * (E ^ k).trace = (E ^ k).trace * E a b := by
  first
  | exact @_root_.GlobalTheory.CommutatorPowerEntry.main
  | exact _root_.GlobalTheory.CommutatorPowerEntry.main
  | (apply _root_.GlobalTheory.CommutatorPowerEntry.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommutatorPowerEntry.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommutatorPowerEntry.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommutatorPowerEntry.main ..)

end GlobalTheory.Alc
