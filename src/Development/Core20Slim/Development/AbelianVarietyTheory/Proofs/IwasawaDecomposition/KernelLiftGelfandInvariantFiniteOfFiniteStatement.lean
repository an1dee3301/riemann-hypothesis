module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelLiftGelfandInvariantFiniteOfFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfConstSmul
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelLift_gelfandInvariantFinite_of_finite : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)), IsKerSys θ V W κ → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ F ∈ Decay θ V, (∃ Z : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Z ∧ F ∈ Z ∧ ∀ τ k, ∀ f ∈ Z, gelf θ V τ k f ∈ Z) → ∀ f, ∃ Z : Submodule ℂ (GA D W → ℂ), FiniteDimensional ℂ Z ∧ (fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) ∈ Z ∧ ∀ τ k, ∀ φ ∈ Z, gelf θ W τ k φ ∈ Z := by
  first | exact @GlobalTheory.Mem.LiftFin.lift_zfin | exact GlobalTheory.Mem.LiftFin.lift_zfin | (intros; apply GlobalTheory.Mem.LiftFin.lift_zfin <;> assumption)
