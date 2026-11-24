module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumAdmissibility
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ThetaMember

section General

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {β : Type} [Fintype β] [DecidableEq β]


theorem exists_dbl_elem {J : Matrix β β E} (g : UG c J) : ∃ gd : UG c (dbl J),
    ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 := by
  have hg : ((g : GL β E) : Matrix β β E)ᵀ * J * ((g : GL β E) : Matrix β β E).map c = J := g.2
  refine ⟨⟨⟨fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1,
    fromBlocks (((g : GL β E)⁻¹ : GL β E) : Matrix β β E) 0 0 1, ?_, ?_⟩, ?_⟩, rfl⟩
  · rw [fromBlocks_multiply, Units.mul_inv]; simp
  · rw [fromBlocks_multiply, Units.inv_mul]; simp
  · change (fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1)ᵀ * dbl J *
      (fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1).map c = dbl J
    rw [fromBlocks_map, fromBlocks_transpose, dbl, fromBlocks_multiply, fromBlocks_multiply,
      Matrix.map_one _ (map_zero c) (map_one c), Matrix.map_zero _ (map_zero c)]
    simp [hg]

end General




end GlobalTheory.CompanionTheory.ThetaMember
