module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHoweDualityIntertwinerUnitaryPairLocal
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalHoweContractionCompactUnitaryStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetTwistedConjugateIsKTypeOfReversedStatement
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_howeDuality_intertwiner_unitaryPair_local : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (x₁ x₃ : ℤ) (Λ : Fin n → ℝ) (Λ' : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (σ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → (∀ a, Λ a = -(x₃ : ℝ) + ν (Fin.castLE hn a)) → (∀ b, Λ' b = (x₁ : ℝ) + ν b) → Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos n)) σ → Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos n) σ Λ ⊤ → Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos N)) σ' → Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos N) σ' Λ' ⊤ → ∃ I : MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] H →ₗ[ℂ] H', I ≠ 0 ∧ ∀ h ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos N), ∀ g ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos n), ∀ P v, I ((h.det ^ x₁ * g.det ^ x₃) • GlobalTheory.CompactHowe.subst2 h (g⁻¹)ᵀ P) (σ g v) = σ' h (I P v) := by
  first | exact @GlobalTheory.CompactHowe.exists_local_lift | exact GlobalTheory.CompactHowe.exists_local_lift | (intros; apply GlobalTheory.CompactHowe.exists_local_lift <;> assumption)
