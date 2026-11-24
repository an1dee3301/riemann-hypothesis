module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
public import Development.Core20Slim.Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

variable {D : D7}

theorem analyticOnNhd_of_differentiable_vc {N N' : ℕ} (H : TaylorLogMetric.VC D N N' → ℂ) (hH : Differentiable ℂ H) :
    AnalyticOnNhd ℂ H Set.univ := by
  let e : TaylorLogMetric.VC D N N' ≃L[ℂ] (Fin (Module.finrank ℂ (TaylorLogMetric.VC D N N')) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [Module.finrank_fin_fun])
  have h1 : AnalyticOnNhd ℂ (H ∘ e.symm) Set.univ :=
    ReciprocityTheory.AnForm.Osgood.osgood _ Set.univ (H ∘ e.symm) isOpen_univ
      (hH.comp e.symm.differentiable).differentiableOn
  have h2 : H = (H ∘ e.symm) ∘ e := by
    funext z
    simp
  rw [h2]
  exact h1.comp (e.toContinuousLinearMap.analyticOnNhd Set.univ) (Set.mapsTo_univ _ _)


end GlobalTheory
