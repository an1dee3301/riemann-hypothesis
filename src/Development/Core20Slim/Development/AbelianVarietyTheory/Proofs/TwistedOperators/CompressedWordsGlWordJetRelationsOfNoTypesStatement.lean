module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompressedWordsGlWordJetRelationsOfNoTypes
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Formalism.RealPlaceAnalysis.StatementA
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compressedWords_glWordJetRelations_of_no_types : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V), LowData ε E Λ u j → (∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ x : V, KHighest ε E (Λ - root a b) x → x = 0) → JetRel ε E Λ u j (modJet E j) := by
  first | exact @GlobalTheory.SphJet.ModRel.modJet_jetRel | exact GlobalTheory.SphJet.ModRel.modJet_jetRel | (intros; apply GlobalTheory.SphJet.ModRel.modJet_jetRel <;> assumption)
