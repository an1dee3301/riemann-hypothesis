module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlWordJetRelationsEqZeroOfNil
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Formalism.RealPlaceAnalysis.StatementU
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init

@[expose] public section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glWordJetRelations_eq_zero_of_nil : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) (B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), LowData ε E (LamOf ε lam) u j → (∀ a b : Fin n, a < b → ε a ≠ ε b → 2 * (n : ℝ) + 1 ≤ lam a - lam b) → JetRel ε E (LamOf ε lam) u j B → B [] = 0 → ∀ l, B l = 0 := by
  first | exact @GlobalTheory.SphJet.jetRel_eq_zero_of_nil | exact GlobalTheory.SphJet.jetRel_eq_zero_of_nil | (intros; apply GlobalTheory.SphJet.jetRel_eq_zero_of_nil <;> assumption)
