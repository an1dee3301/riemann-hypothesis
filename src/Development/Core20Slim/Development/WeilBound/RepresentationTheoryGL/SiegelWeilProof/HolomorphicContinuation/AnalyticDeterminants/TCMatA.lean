module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopCompS
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ContDiffOnSecondCayleyBlockEntries
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ReidxConjTranspose
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem cm_mul_cmI : Cm n * CmI n = 1 := by
  rw [Cm, CmI, Matrix.mul_smul, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul, fromBlocks_inj]
  simp [smul_smul]
  have h : -(Complex.I * 2⁻¹ * Complex.I + Complex.I * 2⁻¹ * Complex.I) = 1 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← neg_add, ← add_smul, ← neg_smul, h, one_smul]

theorem cmI_mul_cm : CmI n * Cm n = 1 := by
  rw [Cm, CmI, Matrix.smul_mul, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul, fromBlocks_inj]
  simp [smul_smul]
  have h : -(Complex.I * 2⁻¹ * Complex.I + Complex.I * 2⁻¹ * Complex.I) = 1 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← neg_add, ← add_smul, ← neg_smul, h, one_smul]

theorem cm_inv : (Cm n)⁻¹ = CmI n := Matrix.inv_eq_right_inv cm_mul_cmI

theorem cmH_JJ_cm : (Cm n)ᴴ * JJ n * Cm n = fromBlocks ((-(2 * Complex.I)) • 1) 0 0 ((2 * Complex.I) • 1) := by
  rw [Cm, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  simp [smul_smul]
  refine ⟨?_, ?_⟩
  · rw [← neg_add, ← add_smul, two_mul]
  · rw [← add_smul, two_mul]

end PositivityTheory.Rg.Sw.LVs.TC
