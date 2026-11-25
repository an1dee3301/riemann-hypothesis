module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTensorEmbedding
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometric_tensor_embedding_intertwining : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T) (πU : URep T) (v : D.HK.V), ‖D.ι v‖ = 1 → ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (j : K →ₗᵢ[ℂ] πU.H), (∀ g y y', inner ℂ (j y) (πU.π g (j y')) = mcoef D v g * inner ℂ y y') → (∀ y, ∃ io : D.U.H →L[ℂ] πU.H, IsHomG D πU io ∧ io (D.ι v) = j y) → ∃ Tm : D.U.H →L[ℂ] K →L[ℂ] πU.H, (∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y') ∧ (∀ y, Tm (D.ι v) y = j y) ∧ (∀ g x y, πU.π g (Tm x y) = Tm (D.U.π g x) y) ∧ ∀ (R : πU.H →L[ℂ] πU.H) (S : K →L[ℂ] K), (∀ g z, R (πU.π g z) = πU.π g (R z)) → (∀ y, R (j y) = j (S y)) → ∀ x y, R (Tm x y) = Tm x (S y) := by
  first | exact @GlobalTheory.FockTensor.exists_tensor_embedding | exact GlobalTheory.FockTensor.exists_tensor_embedding | (intros; apply GlobalTheory.FockTensor.exists_tensor_embedding <;> assumption)
