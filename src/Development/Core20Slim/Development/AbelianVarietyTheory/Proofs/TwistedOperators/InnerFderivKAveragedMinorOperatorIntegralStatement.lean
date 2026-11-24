module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerFderivKAveragedMinorOperatorIntegral
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Init.Data.Cast
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_fderiv_kAveragedMinorOperator_integral : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ z ∈ U1 ε, ∀ (A : Matrix (Fin n) (Fin n) ℂ) (y x : W), Integrable (fun k : KG ε => fderiv ℂ (Phi lam) ((toMK k)⁻¹ * z * toMK k) ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ)) (muK ε) ∧ ⟪y, fderiv ℂ (ps ε lam τ w) z A x⟫_ℂ = (Module.finrank ℂ W : ℂ) * ∫ k : KG ε, fderiv ℂ (Phi lam) ((toMK k)⁻¹ * z * toMK k) ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ) ∂(muK ε) := by
  first | exact @GlobalTheory.SphJet.PsDer.inner_fderiv_ps | exact GlobalTheory.SphJet.PsDer.inner_fderiv_ps | (intros; apply GlobalTheory.SphJet.PsDer.inner_fderiv_ps <;> assumption)
