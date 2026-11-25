module
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LGradedLemmas
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.StatementB
public import Development.Core20Slim.Formalism.PieriBlockIdeals.PieriColumnMinors.RowGenDerivative
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous


@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility  


theorem hw_norm_pos {r : ℕ} (ν : Fin r → ℕ) : 0 < fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) :=
  (fockQPos _ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν)).2 (hwNe ℚ r r le_rfl ν)




theorem coeff_der_diag {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ) (m : Fin r × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (der r n a a f) m = ((Finsupp.weight (rowW r n) m a : ℕ) : ℚ) * AddMonoidAlgebra.coeff f m := by
  rw [← rowDiv_one, lgraded_coeff_euler, lgraded_weight_rowW]

theorem der_diag_iff {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) ℚ) (μ : Fin r → ℕ) :
    IsWeightedHomogeneous (rowW r n) f μ ↔ ∀ a, der r n a a f = (μ a : ℚ) • f := by
  constructor
  · intro h a
    ext m
    rw [coeff_der_diag, coeff_smul, smul_eq_mul]
    by_cases hm : AddMonoidAlgebra.coeff f m = 0
    · rw [hm, mul_zero, mul_zero]
    · rw [h hm]
  · intro h m hm
    funext a
    have h1 := congrArg (AddMonoidAlgebra.coeff · m) (h a)
    rw [coeff_der_diag, coeff_smul, smul_eq_mul] at h1
    exact_mod_cast mul_right_cancel₀ hm h1



theorem rowNu_self {r : ℕ} (ν : Fin r → ℕ) : rowNu (r := r) ν = ν := by
  funext a
  simp [rowNu, a.isLt]

theorem hw_rowHom {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) :
    IsWeightedHomogeneous (rowW r r) (hw ℚ le_rfl ν) ν := by
  have h := hwRowWeight ℚ r r le_rfl ν hν
  rwa [rowNu_self] at h

theorem der_hw_raise {r : ℕ} (ν : Fin r → ℕ) (a b : Fin r) (hab : a < b) : der r r a b (hw ℚ le_rfl ν) = 0 := by
  rw [← rowDiv_one]
  exact hwRaise ℚ r r le_rfl ν a b 1 hab le_rfl









end Formalism.CohomologicalDescent.LR
