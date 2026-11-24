module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactUnitaryKernelConcentratedNearOne
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivative
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compactUnitaryKernel_concentrated_near_one : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, ∃ κ : KG ε → ℝ, Continuous κ ∧ (∀ k, 0 ≤ κ k) ∧ ∫ k, κ k ∂(muK ε) = 1 ∧ (fun k => (κ k : ℂ)) ∈ polyV ε m ∧ ∫ k, κ k * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε) ≤ C * ((m : ℝ) + 1) ^ (-(1 / 4 : ℝ)) := by
  first | exact @GlobalTheory.KFourier.kernel_near_one | exact GlobalTheory.KFourier.kernel_near_one | (intros; apply GlobalTheory.KFourier.kernel_near_one <;> assumption)
