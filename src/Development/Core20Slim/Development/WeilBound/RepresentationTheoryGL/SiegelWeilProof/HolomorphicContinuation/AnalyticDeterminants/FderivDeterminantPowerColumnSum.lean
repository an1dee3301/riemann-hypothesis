module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.AnalyticAtDeterminantPowerZeroInt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.AnalyticAtDet
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DetColumnPerturbation
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.FderivDeterminantPowerCornerInt
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {N : ℕ}

def fsum (t : ℤ) (c : Fin N) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) : ℂ :=
  -∑ k, X k 0 * fderiv ℂ (H N t) (piF X) (Matrix.single k c 1)

theorem colQ_expand (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (c : Fin N) :
    colQ X c = ∑ k, X k 0 • Matrix.single k c (1 : ℂ) := by
  ext k l
  simp only [colQ, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  split_ifs with h
  · subst h
    simp
  · simp [Ne.symm h]

theorem fderiv_determinant_power_column_sum (t : ℤ) (X : Matrix (Fin N) (Fin (N + 1)) ℂ) (hX : (1 + piF X).det ≠ 0) (c : Fin N) :
    fderiv ℂ (H (N + 1) t) (phiF X) (Matrix.single 0 c.succ 1) = fsum t c X := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fderiv_determinant_power_column_int t X hX c, colQ_expand, map_sum, fsum]
  simp only [map_smul, smul_eq_mul]

theorem analyticAt_entry (k : Fin N) (j : Fin (N + 1)) (X0 : Matrix (Fin N) (Fin (N + 1)) ℂ) :
    AnalyticAt ℂ (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => X k j) X0 := by
  have := (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℂ ℂ k j : Matrix (Fin N) (Fin (N + 1)) ℂ →ₗ[ℂ] ℂ)).analyticAt X0
  exact this

theorem analyticAt_piF (X0 : Matrix (Fin N) (Fin (N + 1)) ℂ) :
    AnalyticAt ℂ (piF : Matrix (Fin N) (Fin (N + 1)) ℂ → Matrix (Fin N) (Fin N) ℂ) X0 :=
  (piL N).analyticAt X0

theorem analyticAt_fsum (t : ℤ) (c : Fin N) (X0 : Matrix (Fin N) (Fin (N + 1)) ℂ) (h : (1 + piF X0).det ≠ 0) :
    AnalyticAt ℂ (fsum t c) X0 := by
  have hE : ∀ k : Fin N, AnalyticAt ℂ (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ =>
      X k 0 * fderiv ℂ (H N t) (piF X) (Matrix.single k c 1)) X0 := by
    intro k
    refine (analyticAt_entry k 0 X0).mul ?_
    exact (analyticAt_fderiv_apply (H N t) (piF X0) (Matrix.single k c 1)
      (analyticAt_H N t _ h)).comp (analyticAt_piF X0)
  have hs := (Finset.analyticAt_sum Finset.univ (fun k _ => hE k)).neg
  convert hs using 1
  funext X
  simp [fsum, Finset.sum_apply]

end PositivityTheory.Rg.Sw.LVs.CK
