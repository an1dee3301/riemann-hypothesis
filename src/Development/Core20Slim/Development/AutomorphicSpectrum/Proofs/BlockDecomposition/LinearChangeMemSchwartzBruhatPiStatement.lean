module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearChangeMemSchwartzBruhatPi
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearChange_mem_schwartzBruhatPi : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ∀ {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) (A : GL ι 𝔸[k]), ltr A F ∈ schwartzBruhatPi (K := k) (ι := ι) := by
  first | exact @GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem | exact GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem | (intros; apply GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem <;> assumption)
