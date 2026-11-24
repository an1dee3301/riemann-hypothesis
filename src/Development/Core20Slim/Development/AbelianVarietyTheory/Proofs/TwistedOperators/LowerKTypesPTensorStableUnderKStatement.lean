module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerKTypesPTensorStableUnderK
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.StatementU
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerKTypes_pTensor_stable_under_K : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), LowData ε E Λ u j → IsTau ε Λ τ w → TauTie ε E j τ → ∀ G : Fin n × Fin n → W, arr1 j G ∈ Vminus ε E Λ u → ∀ k ∈ Kset ε, ∃ G' : Fin n × Fin n → W, arr1 j G' ∈ Vminus ε E Λ u ∧ ∑ p, ⟪τ k w, G p⟫_ℂ • (k⁻¹ * thE ε p * k) = ∑ p, ⟪w, G' p⟫_ℂ • thE ε p := by
  first | exact @GlobalTheory.SphJet.vminus_stable_under_K | exact GlobalTheory.SphJet.vminus_stable_under_K | (intros; apply GlobalTheory.SphJet.vminus_stable_under_K <;> assumption)
