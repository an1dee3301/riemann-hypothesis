module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsJointHighestWeightLeadingMinorProduct
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.Core20Slim.ReciprocityTheory.DualLattices.FischerSelfNeZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Development.Core20Slim.ReciprocityTheory.DualLattices.FischerAdjointStatement

@[expose] public section

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jointHighestWeight_leadingMinorProduct : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → ∃ Δ : MvPolynomial (Fin N × Fin n) ℂ, Δ ≠ 0 ∧ (∀ h g, ReciprocityTheory.PGsh.IsUpperUnitri h → ReciprocityTheory.PGsh.IsUpperUnitri g → subst2 h g Δ = Δ) ∧ ∀ (d : Fin N → ℂ) (e : Fin n → ℂ), subst2 (Matrix.diagonal d) (Matrix.diagonal e) Δ = ((∏ b, d b ^ ν b) * ∏ a, e a ^ ν (Fin.castLE hn a)) • Δ := by
  first | exact @GlobalTheory.CompactHowe.Minors.exists_highestWeight | exact GlobalTheory.CompactHowe.Minors.exists_highestWeight | (intros; apply GlobalTheory.CompactHowe.Minors.exists_highestWeight <;> assumption)
