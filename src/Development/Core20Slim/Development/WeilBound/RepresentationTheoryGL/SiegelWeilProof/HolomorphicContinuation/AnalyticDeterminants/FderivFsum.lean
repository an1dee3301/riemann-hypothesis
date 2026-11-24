module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.FderivDeterminantPowerColumnSum
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.AnalyticAtDet
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DetColumnPerturbation
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {N : ℕ}

theorem fsum_line (t : ℤ) (c k0 : Fin N) (y : Matrix (Fin N) (Fin (N + 1)) ℂ) (s : ℂ) :
    fsum t c (y + s • Matrix.single k0 0 1) =
      fsum t c y - s * fderiv ℂ (H N t) (piF y) (Matrix.single k0 c 1) := by
  have hp : piF (y + s • Matrix.single k0 0 1) = piF y := by
    ext k l
    simp [piF, Matrix.single_apply, Fin.succ_ne_zero]
    intro _ h
    exact absurd h.symm (Fin.succ_ne_zero l)
  simp only [fsum, hp]
  (simp [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']) <;> ring

theorem fderiv_fsum (t : ℤ) (c k0 : Fin N) (y : Matrix (Fin N) (Fin (N + 1)) ℂ) (hy : (1 + piF y).det ≠ 0) :
    fderiv ℂ (fsum t c) y (Matrix.single k0 0 1) = -fderiv ℂ (H N t) (piF y) (Matrix.single k0 c 1) := by
  have hd : DifferentiableAt ℂ (fsum t c) y := (analyticAt_fsum t c y hy).differentiableAt
  have hl : HasDerivAt (fun s : ℂ => y + s • Matrix.single k0 0 (1 : ℂ)) (Matrix.single k0 0 1) 0 := by
    have h0 := ((hasDerivAt_id (0 : ℂ)).smul_const (Matrix.single k0 0 (1 : ℂ))).const_add y
    simp only [id_eq, one_smul] at h0
    exact h0
  have h1 : HasDerivAt (fun s : ℂ => fsum t c (y + s • Matrix.single k0 0 1))
      (fderiv ℂ (fsum t c) y (Matrix.single k0 0 1)) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hd.hasFDerivAt hl (by simp)
  have h2 : HasDerivAt (fun s : ℂ => fsum t c (y + s • Matrix.single k0 0 1))
      (-fderiv ℂ (H N t) (piF y) (Matrix.single k0 c 1)) 0 := by
    have he : (fun s : ℂ => fsum t c (y + s • Matrix.single k0 0 1)) =
        fun s => fsum t c y - s * fderiv ℂ (H N t) (piF y) (Matrix.single k0 c 1) :=
      funext fun s => fsum_line t c k0 y s
    rw [he]
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const
      (fderiv ℂ (H N t) (piF y) (Matrix.single k0 c 1))).const_sub (fsum t c y)
  exact h1.unique h2

end PositivityTheory.Rg.Sw.LVs.CK
