module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSummableMajorantLatticeSum
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_summable_majorant_lattice_sum : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ∀ {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) {C : Set (GL ι 𝔸[k])} (hC : IsCompact C), ∃ u : (ι → k) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : ι → k,
      ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ)‖ ≤ u ξ := by
  first | exact @GlobalTheory.CompanionTheory.EisRkNBound.exists_summable_bound_thetaC | exact GlobalTheory.CompanionTheory.EisRkNBound.exists_summable_bound_thetaC | (intros; apply GlobalTheory.CompanionTheory.EisRkNBound.exists_summable_bound_thetaC <;> assumption)
