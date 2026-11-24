module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetTwistedConjugateIsKTypeOfReversed
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.Core20Slim.ReciprocityTheory.DualLattices.FischerSelfNeZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detTwistedConjugate_isKTypeOf_reversed : ∀ (k : ℕ) (Λ : Fin k → ℝ) (x : ℤ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsURepOn (UJset (allPos k)) σ → IsKTypeOf (allPos k) σ Λ ⊤ → IsURepOn (UJset (allPos k)) (fun g => g.det ^ x • σ (g.map star)) ∧ IsKTypeOf (allPos k) (fun g => g.det ^ x • σ (g.map star)) (fun a => (x : ℝ) - Λ (Fin.rev a)) ⊤ := by
  first | exact @GlobalTheory.ConjTwist.conj_twist_isKTypeOf | exact GlobalTheory.ConjTwist.conj_twist_isKTypeOf | (intros; apply GlobalTheory.ConjTwist.conj_twist_isKTypeOf <;> assumption)
