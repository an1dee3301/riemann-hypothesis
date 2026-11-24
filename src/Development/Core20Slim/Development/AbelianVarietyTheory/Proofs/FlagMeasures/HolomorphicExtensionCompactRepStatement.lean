module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.HolomorphicExtensionCompactRep
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.RealPlaceAnalysis.Complexify
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_extension_compact_rep : ∀ (n : ℕ) (ε : Fin n → Bool) (B : Type) [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] (π : Matrix (Fin n) (Fin n) ℂ → B), π 1 = 1 → (∀ a ∈ Formalism.REAL.Kset ε, ∀ b ∈ Formalism.REAL.Kset ε, π (a * b) = π a * π b) → ContinuousOn π (Formalism.REAL.Kset ε) → ∃ τ : Matrix (Fin n) (Fin n) ℂ → B, DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | IsUnit (Matrix.of y)} ∧ ∀ k ∈ Formalism.REAL.Kset ε, τ k = π k := by
  first | exact @GlobalTheory.HolExt.exists_holomorphic_extension | exact GlobalTheory.HolExt.exists_holomorphic_extension | (intros; apply GlobalTheory.HolExt.exists_holomorphic_extension <;> assumption)
