module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedDerivInnerExpEqWordJetForms
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDeriv_inner_exp_eq_wordJetForms : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) [CompleteSpace W] (j : W →ₗᵢ[ℂ] V) (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)), AnalyticAt ℂ f 1 → (∀ l, funJet ε f l = modJet E j l) → ∀ (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (y x : W), iteratedDeriv m (fun t : ℝ => ⟪y, f (NormedSpace.exp ((t : ℂ) • thM ε X)) x⟫_ℂ) 0 = ⟪j y, (actM E X ^ m) (j x)⟫_ℂ := by
  first | exact @GlobalTheory.SphJet.Taylor.iteratedDeriv_inner_exp | exact GlobalTheory.SphJet.Taylor.iteratedDeriv_inner_exp | (intros; apply GlobalTheory.SphJet.Taylor.iteratedDeriv_inner_exp <;> assumption)
