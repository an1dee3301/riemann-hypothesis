module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SatakeDualWeyl.Statement
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

theorem exists_lift_blocks (p q : ℕ) (T : GrpData p q) :
    ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∀ V ∈ Matrix.unitaryGroup (Fin q) ℂ,
      ∃ k ∈ T.Kset, matG T k = Matrix.fromBlocks U 0 0 V := by
  intro U hU V hV
  have hU1 := Matrix.mem_unitaryGroup_iff.1 hU
  have hU2 := Matrix.mem_unitaryGroup_iff'.1 hU
  have hV1 := Matrix.mem_unitaryGroup_iff.1 hV
  have hV2 := Matrix.mem_unitaryGroup_iff'.1 hV
  rw [star_eq_conjTranspose] at hU1 hU2 hV1 hV2
  let g : GL (Ix p q) ℂ :=
    ⟨Matrix.fromBlocks U 0 0 V, Matrix.fromBlocks Uᴴ 0 0 Vᴴ,
      by simp [Matrix.fromBlocks_multiply, hU1, hV1],
      by simp [Matrix.fromBlocks_multiply, hU2, hV2]⟩
  have hg : g ∈ Formalism.UG.Upq p q := by
    show (Matrix.fromBlocks U 0 0 V : Mat p q)ᴴ * Formalism.UG.Jpq p q * Matrix.fromBlocks U 0 0 V
      = Formalism.UG.Jpq p q
    simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU2, hV2]
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((g : GL (Ix p q) ℂ) : Mat p q).det
    (show 0 < 2 by norm_num)
  have hdet : ((g : GL (Ix p q) ℂ) : Mat p q).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hdet (by rw [← hw]; simp)
  obtain ⟨k, ⟨hk, -⟩, -⟩ := T.bij g hg (Units.mk0 w hw0) hw
  have hm : matG T k = Matrix.fromBlocks U 0 0 V := by
    unfold matG; rw [hk]
  refine ⟨k, ?_, hm⟩
  show IsKC (matG T k)
  rw [hm]
  intro a b hab
  cases a <;> cases b <;> simp_all [sameBlock]

end GlobalTheory.PolarU
