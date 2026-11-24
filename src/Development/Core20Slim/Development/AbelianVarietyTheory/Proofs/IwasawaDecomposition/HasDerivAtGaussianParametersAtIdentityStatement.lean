module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtGaussianParametersAtIdentity
public import Formalism.LocalRingCardinality.DataTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_gaussian_parameters_at_identity : ∀ (P Q : ℕ) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (Z : Mat P Q) (g g' : ℝ → Mat P Q), g 0 = 1 → g' 0 = 1 → (∀ a b, HasDerivAt (fun t => g t a b) (Z a b) 0) → (∀ a b, HasDerivAt (fun t => g' t a b) (-Z a b) 0) → (∀ i j, HasDerivAt (fun t => matA (g t * baseY A) i j) (dA Z A i j) 0) ∧ (∀ l, HasDerivAt (fun t => linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t) l) (dX Z A x l) 0) ∧ HasDerivAt (fun t => scal (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t)) (dS Z A x) 0 := by
  first | exact @GlobalTheory.OscGauss.ParDer.par_deriv | exact GlobalTheory.OscGauss.ParDer.par_deriv | (intros; apply GlobalTheory.OscGauss.ParDer.par_deriv <;> assumption)
