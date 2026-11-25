module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLineMatrixKroneckerRightFactor
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit

@[expose] public section

noncomputable section
namespace GlobalTheory.FockLowDiff
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

def ixSign {p q : ℕ} : Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

theorem Jm_eq_diagonal (p q : ℕ) : Jm p q = Matrix.diagonal ixSign := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, ixSign, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem omAct_kron_diagonal {p q r s : ℕ} (Z : Mat p q) (t : Ix r s → ℂ) (P : Pol p q r s) :
    omAct p q r s (Matrix.kroneckerMap (· * ·) Z (Matrix.diagonal t)) P =
      ∑ a, ∑ b, ∑ c, (Z a b * t c) • omE ((a, c) : Ln p q r s) (b, c) P := by
  rw [omAct_apply, Fintype.sum_prod_type, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm (f := fun b c => (Z a b * t c) • omE ((a, c) : Ln p q r s) (b, c) P),
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_prod_type, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LinearMap.sum_apply, Finset.sum_eq_single c]
  · simp
  · intro d _ hd
    simp [Matrix.diagonal_apply_ne _ (Ne.symm hd)]
  · simp

theorem lowering_eq_diff : ∀ (p q r s : ℕ) (Z : Mat p q), IsPC Z → ∀ P : Pol p q r s, omAct p q r s (Matrix.kroneckerMap (· * ·) Z (1 : Mat r s)) P - omAct p q r s (Matrix.kroneckerMap (· * ·) (Jm p q * Z) (Jm r s)) P = (2 : ℂ) • minusPart (fockAct1 p q r s Z) P := by
  intro p q r s Z hZ P
  rw [((GlobalTheory.FockParts.explicit_parts p q r s).1 Z hZ P).2, Jm_eq_diagonal, Jm_eq_diagonal,
    ← Matrix.diagonal_one, omAct_kron_diagonal, omAct_kron_diagonal, ← Finset.sum_sub_distrib,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.diagonal_mul, ← sub_smul]
  by_cases hab : sameBlock a b
  · simp [hZ a b hab]
  · rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp [sameBlock] at hab <;>
      simp [ixSign, linePos, omE, raiB, lowB, two_smul, add_smul, add_comm]

end GlobalTheory.FockLowDiff
