module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.KAveragedMinorOperatorExpPosBoundAnalytic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.RealPlaceAnalysis.Complexify
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
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kAveragedMinorOperator_exp_pos_bound_analytic : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ h : ℝ, GapAtLeast ε lam h → ∀ X, inP ε X → (∀ x : W, 0 ≤ ⟪x, ps ε lam τ w (NormedSpace.exp X) x⟫_ℂ) ∧ ‖ps ε lam τ w (NormedSpace.exp X)‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) ∧ AnalyticAt ℂ (ps ε lam τ w) (NormedSpace.exp X) := by
  first | exact @GlobalTheory.SphJet.ps_exp_pos_bound_analytic | exact GlobalTheory.SphJet.ps_exp_pos_bound_analytic | (intros; apply GlobalTheory.SphJet.ps_exp_pos_bound_analytic <;> assumption)
