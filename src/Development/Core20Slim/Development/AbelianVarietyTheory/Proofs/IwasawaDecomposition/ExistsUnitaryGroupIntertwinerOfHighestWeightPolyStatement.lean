module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryGroupIntertwinerOfHighestWeightPoly
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.Core20Slim.ReciprocityTheory.DualLattices.FischerSelfNeZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
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
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Development.Core20Slim.ReciprocityTheory.DualLattices.FischerAdjointStatement

@[expose] public section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryGroup_intertwiner_of_highest_weight_polynomial : ∀ (k : ℕ) (κ : Type) [Fintype κ] (ν : Fin k → ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (τ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (Δ : MvPolynomial (Fin k × κ) ℂ), IsURepOn (UJset (allPos k)) τ → IsKTypeOf (allPos k) τ (fun a => (ν a : ℝ)) ⊤ → Δ ≠ 0 → (∀ g, ReciprocityTheory.PGsh.IsUpperUnitri g → ReciprocityTheory.PGsh.rowSubst g Δ = Δ) → (∀ d : Fin k → ℂ, ReciprocityTheory.PGsh.rowSubst (Matrix.diagonal d) Δ = (∏ a, d a ^ ν a) • Δ) → ∃ L : H →ₗ[ℂ] MvPolynomial (Fin k × κ) ℂ, (∀ g ∈ UJset (allPos k), ∀ u, L (τ g u) = ReciprocityTheory.PGsh.rowSubst g (L u)) ∧ ∃ v, L v = Δ := by
  first | exact @GlobalTheory.HighestPolynomial.exists_intertwiner | exact GlobalTheory.HighestPolynomial.exists_intertwiner | (intros; apply GlobalTheory.HighestPolynomial.exists_intertwiner <;> assumption)
