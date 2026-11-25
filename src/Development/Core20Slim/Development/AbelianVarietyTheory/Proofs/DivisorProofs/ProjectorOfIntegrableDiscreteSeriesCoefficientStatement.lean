module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorOfIntegrableDiscreteSeriesCoefficient
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
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
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projector_of_integrable_discreteSeries_coefficient : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T) (v : D.HK.V), ‖D.ι v‖ = 1 → MeasureTheory.Integrable (eFun D v) T.haar → (∀ u, opE T D.U.π (eFun D v) u = inner ℂ (D.ι v) u • D.ι v) ∧ ∀ πU : URep T, (∀ x y, inner ℂ (opE T πU.π (eFun D v) x) y = inner ℂ x (opE T πU.π (eFun D v) y)) ∧ (∀ g x, opE T πU.π (eFun D v) (πU.π g (opE T πU.π (eFun D v) x)) = mcoef D v g • opE T πU.π (eFun D v) x) ∧ ∀ ξ, opE T πU.π (eFun D v) ξ = ξ → ∃ io : D.U.H →L[ℂ] πU.H, IsHomG D πU io ∧ io (D.ι v) = ξ ∧ ∀ x, ‖io x‖ = ‖ξ‖ * ‖x‖ := by
  first | exact @GlobalTheory.CoefProjector.projector_of_integrable_coefficient | exact GlobalTheory.CoefProjector.projector_of_integrable_coefficient | (intros; apply GlobalTheory.CoefProjector.projector_of_integrable_coefficient <;> assumption)
