module

public import Mathlib
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.IndexNSmul
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GlobalTheory

theorem relIndex_map_mulLeft_lattice_of_sq_eq_neg :
    ∀ (L : PeriodPair) (α : ℂ) (N : ℕ), 0 < N → α ^ 2 = -(N : ℂ) →
      (∀ l ∈ L.lattice, α * l ∈ L.lattice) →
      (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex L.lattice.toAddSubgroup
        = N := by
  intro L α N hN hα hL
  have hα0 : α ≠ 0 := by
    rintro rfl
    have : (N : ℂ) = 0 := by simpa using hα
    exact hN.ne' (by exact_mod_cast this)
  have hinj : Function.Injective (AddMonoidHom.mulLeft α) := mul_right_injective₀ hα0
  set A := L.lattice.toAddSubgroup with hA
  set f := AddMonoidHom.mulLeft α with hf
  have h1 : A.map f ≤ A := by
    rintro _ ⟨l, hl, rfl⟩
    exact hL l hl
  have h2 : (A.map f).map f ≤ A.map f := AddSubgroup.map_mono h1
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ h2 h1
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hinj] at hmul
  have hr : Module.finrank ℤ L.lattice = 2 := by
    simpa using Module.finrank_eq_card_basis L.latticeBasis
  have hidx : ((A.map f).map f).relIndex A = N ^ 2 := by
    rw [← hr, ← AddSubgroup.index_range_nsmul, AddSubgroup.relIndex]
    congr 1
    ext x
    rw [AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, hx⟩
      refine ⟨⟨-l, L.lattice.neg_mem hl⟩, Subtype.ext ?_⟩
      have hx' : α * (α * l) = (x : ℂ) := hx
      show N • (-l) = (x : ℂ)
      rw [← hx', nsmul_eq_mul]
      linear_combination (-l) * hα
    · rintro ⟨l, hx⟩
      have hx' : N • (l : ℂ) = (x : ℂ) := congrArg Subtype.val hx
      refine ⟨_, ⟨-(l : ℂ), L.lattice.neg_mem l.2, rfl⟩, ?_⟩
      show α * (α * -(l : ℂ)) = (x : ℂ)
      rw [← hx', nsmul_eq_mul]
      linear_combination (-(l : ℂ)) * hα
  rw [hidx, ← sq] at hmul
  exact Nat.pow_left_injective two_ne_zero hmul

end GlobalTheory
