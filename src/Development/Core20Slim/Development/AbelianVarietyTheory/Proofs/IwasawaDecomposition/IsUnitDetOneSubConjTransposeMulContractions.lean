module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem isUnit_det_one_sub_conjTranspose_mul_of_contractions (P Q : ℕ)
    (A B : Matrix (Fin P) (Fin Q) ℂ) (hA : (1 - Aᴴ * A).PosDef) (hB : (1 - Bᴴ * B).PosDef) :
    IsUnit (1 - Aᴴ * B).det := by
  rw [isUnit_iff_ne_zero]
  intro h
  obtain ⟨u, hu, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hsum : ((1 - Aᴴ * A) + (1 - Bᴴ * B) + (A - B)ᴴ * (A - B)).PosDef :=
    (hA.add hB).add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self _)
  have heq : (1 - Aᴴ * A) + (1 - Bᴴ * B) + (A - B)ᴴ * (A - B)
      = (1 - Aᴴ * B) + (1 - Aᴴ * B)ᴴ := by
    simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_mul,
      conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [heq] at hsum
  have hpos := hsum.dotProduct_mulVec_pos hu
  have h2 : star u ⬝ᵥ ((1 - Aᴴ * B)ᴴ *ᵥ u) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, h0]
    simp
  rw [Matrix.add_mulVec, dotProduct_add, h0, h2] at hpos
  simp at hpos

end GlobalTheory
