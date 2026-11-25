module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DetDFin
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {N : ℕ}

def phiF (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := Fin.cons 0 X

def piF (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : Matrix (Fin N) (Fin N) ℂ := fun k l => X k l.succ

def colQ (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (c : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  fun k l => if l = c then X k 0 else 0

@[simp] theorem phiF_zero_row (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (j : Fin (N + 1)) : phiF X 0 j = 0 := rfl

@[simp] theorem phiF_succ_row (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (k : Fin N) (j : Fin (N + 1)) :
    phiF X k.succ j = X k j := rfl

def phiL (N : ℕ) : Matrix (Fin N) (Fin (N + 1)) ℂ →L[ℂ] Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := phiF
      map_add' := fun X Y => by
        ext i j; refine Fin.cases ?_ (fun k => ?_) i <;> simp
      map_smul' := fun a X => by
        ext i j; refine Fin.cases ?_ (fun k => ?_) i <;> simp }

def piL (N : ℕ) : Matrix (Fin N) (Fin (N + 1)) ℂ →L[ℂ] Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := piF
      map_add' := fun X Y => by ext k l; simp [piF]
      map_smul' := fun a X => by ext k l; simp [piF] }

@[simp] theorem piL_apply (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : piL N X = piF X := rfl

theorem phiF_single (k : Fin N) (j : Fin (N + 1)) :
    phiF (Matrix.single k j (1 : ℂ)) = Matrix.single k.succ j 1 := by
  ext i l
  refine Fin.cases ?_ (fun m => ?_) i
  · simp [Matrix.single_apply, (Fin.succ_ne_zero k).symm]
  · simp [Matrix.single_apply, Fin.succ_inj]

theorem piF_single_succ (k : Fin N) (j : Fin N) :
    piF (Matrix.single k j.succ (1 : ℂ)) = Matrix.single k j 1 := by
  ext a b; simp [piF, Matrix.single_apply, Fin.succ_inj]


theorem det_first_row_expansion (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (a : ℂ) (h : ∀ j, A 0 j = if j = 0 then a else 0) :
    A.det = a * (A.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single 0]
  · simp [h]
  · intro j _ hj; simp [h, hj]
  · simp



end PositivityTheory.Rg.Sw.LVs.CK
