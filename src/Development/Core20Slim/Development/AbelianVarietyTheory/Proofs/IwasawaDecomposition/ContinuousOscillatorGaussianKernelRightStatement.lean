module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOscillatorGaussianKernelRight
public import Formalism.LocalRingCardinality.DataTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_oscillatorGaussianKernel_right : ∀ (P Q : ℕ) (T : Type) [TopologicalSpace T] (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) (Y' : T → Matrix (Ix P Q) (Fin Q) ℂ) (v' φ' : T → Ix P Q → ℂ), Continuous Y' → Continuous v' → Continuous φ' → (∀ t, IsUnit (Yᴴ * Jm P Q * Y' t).det) → Continuous fun t => ker Y v φ (Y' t) (v' t) (φ' t) := by
  first | exact @GlobalTheory.OscGauss.continuous_ker_right | exact GlobalTheory.OscGauss.continuous_ker_right | (intros; apply GlobalTheory.OscGauss.continuous_ker_right <;> assumption)
