module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section
namespace GlobalTheory.PolarU
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
open scoped Kronecker

section general
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def kronLeftHom (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    Matrix m m ℂ →+* Matrix (m × n) (m × n) ℂ where
  toFun Y := Y ⊗ₖ (1 : Matrix n n ℂ)
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  map_zero' := Matrix.zero_kronecker _
  map_add' A B := Matrix.add_kronecker _ _ _

def kronRightHom (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    Matrix n n ℂ →+* Matrix (m × n) (m × n) ℂ where
  toFun Z := (1 : Matrix m m ℂ) ⊗ₖ Z
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  map_zero' := Matrix.kronecker_zero _
  map_add' A B := Matrix.kronecker_add _ _ _

theorem continuous_kronLeftHom : Continuous (kronLeftHom m n) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun Y : Matrix m m ℂ => Y i.1 j.1 * (1 : Matrix n n ℂ) i.2 j.2
  exact (continuous_apply_apply i.1 j.1).mul continuous_const

theorem continuous_kronRightHom : Continuous (kronRightHom m n) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun Z : Matrix n n ℂ => (1 : Matrix m m ℂ) i.1 j.1 * Z i.2 j.2
  exact continuous_const.mul (continuous_apply_apply i.2 j.2)

theorem exp_kronecker_one (Y : Matrix m m ℂ) :
    NormedSpace.exp (Y ⊗ₖ (1 : Matrix n n ℂ)) = NormedSpace.exp Y ⊗ₖ (1 : Matrix n n ℂ) := by

  open Norms.Operator in
  exact (NormedSpace.map_exp (kronLeftHom m n) continuous_kronLeftHom Y).symm

theorem exp_one_kronecker (Z : Matrix n n ℂ) :
    NormedSpace.exp ((1 : Matrix m m ℂ) ⊗ₖ Z) = (1 : Matrix m m ℂ) ⊗ₖ NormedSpace.exp Z := by
  open Norms.Operator in
  exact (NormedSpace.map_exp (kronRightHom m n) continuous_kronRightHom Z).symm

end general

theorem kronecker_transpose_mulVec_vecM {p q : ℕ} (A B V : Mat p q) :
    (A ⊗ₖ Bᵀ) *ᵥ vecM V = vecM (A * V * B) := by
  funext ab
  obtain ⟨a, b⟩ := ab
  simp only [vecM, Matrix.mulVec, dotProduct, Matrix.kronecker_apply, Matrix.transpose_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem exp_adMat_mulVec (p q : ℕ) (Y V : Mat p q) :
    NormedSpace.exp (adMat Y) *ᵥ vecM V =
      vecM (NormedSpace.exp Y * V * NormedSpace.exp (-Y)) := by

  have hsplit : adMat Y = Y ⊗ₖ (1 : Mat p q) + (1 : Mat p q) ⊗ₖ (-Yᵀ) := by
    rw [adMat, sub_eq_add_neg]
    congr 1
    ext i j
    simp [Matrix.kronecker_apply, Matrix.kroneckerMap_apply]
  have hcomm : Commute (Y ⊗ₖ (1 : Mat p q)) ((1 : Mat p q) ⊗ₖ (-Yᵀ)) := by
    show _ * _ = _ * _
    simp only [← Matrix.mul_kronecker_mul, one_mul, mul_one]
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, exp_kronecker_one, exp_one_kronecker,
    ← Matrix.mul_kronecker_mul, mul_one, one_mul, ← Matrix.transpose_neg, Matrix.exp_transpose]
  exact kronecker_transpose_mulVec_vecM _ _ _

end GlobalTheory.PolarU
