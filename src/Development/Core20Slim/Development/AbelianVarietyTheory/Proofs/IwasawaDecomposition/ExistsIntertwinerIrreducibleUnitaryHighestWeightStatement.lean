module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerIrreducibleUnitaryHighestWeight
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.Core20Slim.ReciprocityTheory.DualLattices.FischerSelfNeZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Formalism.RealPlaceAnalysis.Complexify
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intertwiner_with_highestWeight_vector_in_range : ∀ (k : ℕ) (Λ : Fin k → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (π : Matrix (Fin k) (Fin k) ℂ → (E →L[ℂ] E)) (Δ : E), IsURepOn (UJset (allPos k)) τ → IsKTypeOf (allPos k) τ Λ ⊤ → IsURepOn (UJset (allPos k)) π → (∀ w : E, DifferentiableAt ℂ (fun g : Fin k → Fin k → ℂ => π (Matrix.of g) w) (fun i j => (1 : Matrix (Fin k) (Fin k) ℂ) i j)) → Δ ≠ 0 → (∀ a b : Fin k, a < b → ∀ s : ℂ, π (1 + Matrix.single a b s) Δ = Δ) → IsWtOn (Formalism.REAL.Kset (allPos k)) π Λ Δ → ∃ L : H →ₗ[ℂ] E, (∀ g ∈ UJset (allPos k), ∀ u, L (τ g u) = π g (L u)) ∧ ∃ v, L v = Δ := by
  first | exact @GlobalTheory.HighestWeightMap.exists_intertwiner | exact GlobalTheory.HighestWeightMap.exists_intertwiner | (intros; apply GlobalTheory.HighestWeightMap.exists_intertwiner <;> assumption)
