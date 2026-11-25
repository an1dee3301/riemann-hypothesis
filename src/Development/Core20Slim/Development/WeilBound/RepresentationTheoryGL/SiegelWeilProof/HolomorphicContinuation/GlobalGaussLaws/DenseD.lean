module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.DenseP

variable {n : ℕ}

theorem isUnit_det_of_inG {g : M2 n} (hg : InG g) : IsUnit g.det := by
  have hJ : JJ n * JJ n = -1 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp [JJ, Matrix.fromBlocks_multiply]
  have h1 : (JJ n).det * (JJ n).det = (-1 : ℂ) ^ (Fintype.card (Fin n ⊕ Fin n)) := by
    rw [← Matrix.det_mul, hJ, Matrix.det_neg, Matrix.det_one, mul_one]
  have hJd : (JJ n).det ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h1; exact (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) h1.symm
  have e := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul] at e
  refine isUnit_iff_ne_zero.2 fun h0 => hJd ?_
  rw [h0, mul_zero] at e
  exact e.symm

def mkGR (g : M2 n) (hg : InG g) : GR n :=
  ⟨⟨g, g⁻¹, Matrix.mul_nonsing_inv g (isUnit_det_of_inG hg), Matrix.nonsing_inv_mul g (isUnit_det_of_inG hg)⟩, hg⟩

def IsNElt (g : GR n) : Prop := ∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR g = nU b

def IsMElt (g : GR n) : Prop :=
  ∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR g = fromBlocks a 0 0 (a⁻¹)ᴴ

def IsWElt (g : GR n) : Prop := mR g = JJ n

def GenSt : Prop :=
  ∀ n : ℕ, ∀ g : GR n, g ∈ Subgroup.closure {h : GR n | IsNElt h ∨ IsMElt h ∨ IsWElt h}

end PositivityTheory.Rg.Sw.Glob.DenseP
