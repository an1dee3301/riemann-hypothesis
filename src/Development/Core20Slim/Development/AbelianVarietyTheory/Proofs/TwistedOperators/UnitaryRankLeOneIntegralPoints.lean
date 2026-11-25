module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Omega.Logic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem smallRank : SmallRank := by
  intro L _ _ ϖ σ q n hU hn g

  set A : Matrix (Fin n) (Fin n) L := ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hAdef
  set B : Matrix (Fin n) (Fin n) L := (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
    with hBdef
  have hAB : A * B = 1 := (g : GL (Fin n) L).mul_inv
  have hBA : B * A = 1 := (g : GL (Fin n) L).inv_mul

  have hherm : (A.map σ)ᵀ * antiJ L n * A = antiJ L n := g.2

  have key : ∀ i j, Valued.v (A i j) = 1 ∧ Valued.v (B i j) = 1 := by
    intro i j
    obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · exact i.elim0
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      have h1 : σ (A 0 0) * A 0 0 = 1 := by
        simpa [Matrix.mul_apply, antiJ] using congrFun (congrFun hherm 0) 0
      have h2 : B 0 0 * A 0 0 = 1 := by
        simpa [Matrix.mul_apply] using congrFun (congrFun hBA 0) 0
      have hsq : Valued.v (A 0 0) * Valued.v (A 0 0) = 1 := by
        have := congrArg Valued.v h1
        rwa [map_mul, map_one, hU.2.1] at this
      have hle : Valued.v (A 0 0) ≤ 1 := by
        by_contra hlt
        have hgt : 1 < Valued.v (A 0 0) := not_le.1 hlt
        have : Valued.v (A 0 0) * 1 ≤ Valued.v (A 0 0) * Valued.v (A 0 0) := by gcongr
        rw [mul_one, hsq] at this
        exact hlt this
      have hA1 : Valued.v (A 0 0) = 1 := by
        refine le_antisymm hle ?_
        have : Valued.v (A 0 0) * Valued.v (A 0 0) ≤ Valued.v (A 0 0) * 1 := by gcongr
        rwa [mul_one, hsq] at this
      refine ⟨hA1, ?_⟩
      have := congrArg Valued.v h2
      rwa [map_mul, map_one, hA1, mul_one] at this
  have hint : ∀ x : L, Valued.v x = 1 → x ∈ intL L := fun x hx => by
    unfold intL
    exact (Valuation.mem_integer_iff _ _).2 hx.le

  let A' : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨A i j, hint _ (key i j).1⟩
  let B' : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨B i j, hint _ (key i j).2⟩
  have hinj : Function.Injective
      ((intL L).subtype.mapMatrix : Matrix (Fin n) (Fin n) (intL L) → Matrix (Fin n) (Fin n) L) :=
    fun X Y h => by
      ext i j
      exact congrFun (congrFun h i) j
  have eA : (intL L).subtype.mapMatrix A' = A := rfl
  have eB : (intL L).subtype.mapMatrix B' = B := rfl
  unfold KU
  rw [Subgroup.mem_subgroupOf]
  unfold intPts
  rw [Subgroup.mem_inf, MonoidHom.mem_range]
  refine ⟨g.2, ⟨A', B', hinj ?_, hinj ?_⟩, ?_⟩
  · rw [map_mul, eA, eB, map_one, hAB]
  · rw [map_mul, eA, eB, map_one, hBA]
  · unfold bc
    exact Units.ext eA

end GlobalTheory.InertZeta

end
