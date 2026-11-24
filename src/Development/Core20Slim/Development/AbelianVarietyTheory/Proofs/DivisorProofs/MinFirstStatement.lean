module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jointHarm_highestWeight_and_map_mem_genSub : ∀ (p q r s : ℕ) (M1 : GKMod p q) (M2 : GKMod r s) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M1.V M2.V), IrrGK M1 → AdmGK M1 → Intw M1 M2 f → f ≠ 0 → ∀ (μ : Ix p q → ℚ), (∃ v, IsHW M1.act μ v) → (∀ ν w, IsHW M1.act ν w → degW (cPair r s) μ ≤ degW (cPair r s) ν) → (∃ (μ' : Ix r s → ℚ) (P : Pol p q r s), P ∈ jointHarm p q r s ∧ IsHW (fockAct1 p q r s) μ P ∧ IsHW (fockAct2 p q r s) μ' P ∧ f P ≠ 0) ∧ ∀ P, OfType (fockAct1 p q r s) μ P → f P ∈ Submodule.map f (genSub (fockAct2 p q r s) {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct1 p q r s) μ Q}) := by
  first | exact @GlobalTheory.FockAlg.min_first | exact GlobalTheory.FockAlg.min_first | (intros; apply GlobalTheory.FockAlg.min_first <;> assumption)
