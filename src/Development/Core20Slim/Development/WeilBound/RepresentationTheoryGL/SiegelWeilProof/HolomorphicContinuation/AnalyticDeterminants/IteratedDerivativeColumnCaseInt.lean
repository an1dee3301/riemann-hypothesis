module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.FderivFsum
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.AnalyticAtDet
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.AnalyticAtDeterminantPowerZeroInt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DetColumnPerturbation
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DetDFin
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.FderivDeterminantPowerColumnSum
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem iterated_derivative_column_case_int (t : ℤ) (M : ℕ) (e : Equiv.Perm (Fin (M + 1))) (c : Fin (M + 1)) :
    iteratedFDeriv ℂ (M + 1) (fun y => fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) 0
        (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm (c.succ, e) k.succ) 1) =
      -iteratedFDeriv ℂ (M + 1) (H (M + 1) t) 0 (fun k => Matrix.single k (e k) 1) := by
  have hσ : ∀ k : Fin (M + 1), Equiv.Perm.decomposeFin.symm (c.succ, e) k.succ =
      Equiv.swap 0 c.succ (e k).succ :=
    fun k => Equiv.Perm.decomposeFin_symm_apply_succ e c.succ k
  have hG : AnalyticAt ℂ (fun y : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) ℂ =>
      fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) 0 :=
    analyticAt_fderiv_apply _ 0 _ (analyticAt_determinant_power_zero_int _ t)
  have e1 := icompL (fun y : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) ℂ =>
      fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) phiF phiF_add phiF_smul 0 0
    phiF_zero hG (M + 1)
    (fun k => Matrix.single k (Equiv.swap 0 c.succ (e k).succ) 1)
    (fun k => Matrix.single k.succ (Equiv.Perm.decomposeFin.symm (c.succ, e) k.succ) 1)
    (fun i => by rw [phiF_single, hσ])
  rw [← e1]
  have hev : (fun y : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) ℂ =>
      fderiv ℂ (H (M + 1 + 1) t) y (Matrix.single 0 c.succ 1)) ∘ phiF =ᶠ[𝓝 0] fsum t c := by
    filter_upwards [ev_piF (M + 1)] with X hX
    exact fderiv_determinant_power_column_sum t X hX c
  rw [(hev.iteratedFDeriv ℂ (M + 1)).eq_of_nhds]
  have h0 : (1 + piF (0 : Matrix (Fin (M + 1)) (Fin (M + 1 + 1)) ℂ)).det ≠ 0 := by
    simp [piF_zero]
  rw [ipeel (fsum t c) 0 (analyticAt_fsum t c 0 h0) M _ (e.symm c)]
  beta_reduce
  have hu0 : Equiv.swap 0 c.succ (e (e.symm c)).succ = 0 := by simp
  rw [hu0]
  have hev2 : (fun y => fderiv ℂ (fsum t c) y (Matrix.single (e.symm c) 0 1)) =ᶠ[𝓝 0]
      (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ =>
        (-1 : ℂ) * fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1)) ∘ piF := by
    filter_upwards [ev_piF (M + 1)] with y hy
    simp [fderiv_fsum t c (e.symm c) y hy]
  erw [(hev2.iteratedFDeriv ℂ M).eq_of_nhds]
  have hK : AnalyticAt ℂ (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ =>
      fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1)) 0 :=
    analyticAt_fderiv_apply _ 0 _ (analyticAt_determinant_power_zero_int _ t)
  have hK' : AnalyticAt ℂ (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ =>
      (-1 : ℂ) * fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1)) 0 :=
    analyticAt_const.mul hK
  have hne : ∀ k : Fin M, Equiv.swap 0 c.succ (e ((e.symm c).succAbove k)).succ =
      (e ((e.symm c).succAbove k)).succ := by
    intro k
    have h1 : e ((e.symm c).succAbove k) ≠ c := by
      intro h
      have h2 := congrArg e.symm h
      rw [Equiv.symm_apply_apply] at h2
      exact Fin.succAbove_ne _ _ h2
    exact Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun h => h1 (Fin.succ_injective _ h))
  erw [icompL (fun Z : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ =>
      (-1 : ℂ) * fderiv ℂ (H (M + 1) t) Z (Matrix.single (e.symm c) c 1))
    piF piF_add piF_smul 0 0 piF_zero hK' M
    (fun k => Matrix.single ((e.symm c).succAbove k)
      (Equiv.swap 0 c.succ (e ((e.symm c).succAbove k)).succ) 1)
    (fun k => Matrix.single ((e.symm c).succAbove k) (e ((e.symm c).succAbove k)) 1)
    (fun k => by rw [hne, piF_single_succ])]
  rw [iconst_mul _ 0 (-1) hK]
  rw [ipeel (H (M + 1) t) 0 (analyticAt_determinant_power_zero_int _ t) M (fun k => Matrix.single k (e k) 1) (e.symm c)]
  clear e1 hev hev2 hK' hne hσ hG h0 hu0 hK
  simp
  rfl

end PositivityTheory.Rg.Sw.LVs.CK
