module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFunctionEquivalence
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Formalism.FormalDegreeBessel.StatementDS
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowest_K_type_function_equivalence : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (u : V) (j : W →ₗᵢ[ℂ] V), LowData ε E (lowK ε lam) u j → TauTie ε E j τ → FunEquiv ε E j (ps ε lam τ w) := by
  first | exact @GlobalTheory.SphJet.PsEquivar.psFunEquiv | exact GlobalTheory.SphJet.PsEquivar.psFunEquiv | (intros; apply GlobalTheory.SphJet.PsEquivar.psFunEquiv <;> assumption)
