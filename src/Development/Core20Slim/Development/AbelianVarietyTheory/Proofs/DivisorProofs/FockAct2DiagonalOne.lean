module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.VacuumWeight

theorem diagonal_eq_sum_Eab {r s : ℕ} (D : Ix r s → ℂ) :
    Matrix.diagonal D = ∑ c, D c • Eab c c := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Eab, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]; symm
    exact Finset.sum_eq_zero fun c _ => if_neg fun hc => h (hc.1.symm.trans hc.2)

theorem sum_lineSign {p q r s : ℕ} (c : Ix r s) :
    ∑ a : Ix p q, lineSign a c = ((p : ℂ) - q) * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) c := by
  rcases c with c | c <;> simp [Fintype.sum_sum_type, lineSign] <;> ring

theorem fockAct2_diagonal_one (p q r s : ℕ) (D : Ix r s → ℂ) :
    fockAct2 p q r s (Matrix.diagonal D) (1 : Formalism.BasicNotions.TH.Pol p q r s) =
    ((((p : ℂ) - q) / 2) * ∑ c, D c * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) c) • (1 : Formalism.BasicNotions.TH.Pol p q r s) := by
  have h1 : (1 : Formalism.BasicNotions.TH.Pol p q r s) = MvPolynomial.monomial 0 1 := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [diagonal_eq_sum_Eab, map_sum, LinearMap.sum_apply, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, LinearMap.smul_apply, h1, cartan2, smul_smul]
  congr 1
  simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_add]
  rw [← Finset.sum_mul, sum_lineSign]
  ring

end GlobalTheory.VacuumWeight
