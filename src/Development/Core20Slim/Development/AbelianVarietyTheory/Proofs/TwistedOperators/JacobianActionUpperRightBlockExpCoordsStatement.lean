module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobianActionUpperRightBlockExpCoords
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobian_action_upperRightBlock_exp_coords : ∀ (p q : ℕ) (g : Mat p q) (ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ)), Continuous ψ → (∀ B, ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ, NormedSpace.exp (pY B) * g = Matrix.fromBlocks U 0 0 V * NormedSpace.exp (pY (ψ B))) → (∀ B : Fin p → Fin q → ℂ, 0 < LinearMap.det (sP (pY B))) → (∀ B C : Fin p → Fin q → ℂ, sAd (pY B) (pY C) = pY (sP (pY B) C)) → (∀ B : Fin p → Fin q → ℂ, ∃ A : (Fin p → Fin q → ℂ) →L[ℝ] (Ix p q → Ix p q → ℂ), HasStrictFDerivAt (fun (C : Fin p → Fin q → ℂ) (a b : Ix p q) => NormedSpace.exp (pY C + pY C) a b) A B ∧ ∀ C, Matrix.of (A C) = NormedSpace.exp (pY B) * sAd (pY B) (pY C + pY C) * NormedSpace.exp (pY B)) → ∀ B, ∃ P : (Fin p → Fin q → ℂ) →L[ℝ] (Fin p → Fin q → ℂ), HasFDerivAt ψ P B ∧ |P.det| * LinearMap.det (sP (pY (ψ B))) = LinearMap.det (sP (pY B)) := by
  first | exact @GlobalTheory.PolarU.jacobian_action_p | exact GlobalTheory.PolarU.jacobian_action_p | (intros; apply GlobalTheory.PolarU.jacobian_action_p <;> assumption)
