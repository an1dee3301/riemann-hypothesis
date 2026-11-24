module

public import Mathlib
public import Development.Core20Slim.GroundTheory.LocalFields.AbstractLocalReciprocity.ProfiniteInteger
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Dvd
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.PNat.Defs
public import Mathlib.Data.PNat.Notation
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace GroundTheory.LocalField.Abstract

open scoped GroundTheory.LocalField.Abstract

namespace ProfiniteInteger

def multiples (n : ℕ) : AddSubgroup ℤ̂ :=
  (AddMonoidHom.mulLeft (n : ℤ̂)).range

theorem mem_multiples {n : ℕ} {x : ℤ̂} : x ∈ multiples n ↔ ∃ y : ℤ̂, x = n • y := by
  simp only [multiples, AddMonoidHom.mem_range, AddMonoidHom.coe_mulLeft, nsmul_eq_mul]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩

theorem proj_eq_val_cast {n k : ℕ+} (h : (n : ℕ) ∣ k) (x : ℤ̂) :
    proj n x = ((proj k x).val : ZMod n) := by
  rw [← castHom_proj h x, ZMod.castHom_apply, ZMod.cast_eq_val]

theorem proj_surjective (n : ℕ+) : Function.Surjective (proj n) := fun z =>
  ⟨((z.val : ℕ) : ℤ̂), by rw [map_natCast, ZMod.natCast_zmod_val]⟩

theorem exists_eq_nsmul_of_proj_eq_zero {n : ℕ+} {x : ℤ̂} (hx : proj n x = 0) :
    ∃ y : ℤ̂, x = (n : ℕ) • y := by

  let v : ℕ+ → ℕ := fun m => (proj (n * m) x).val
  have hdvd : ∀ m : ℕ+, (n : ℕ) ∣ v m := by
    intro m
    have h := proj_eq_val_cast (n := n) (k := n * m) (by simp) x
    rw [hx, eq_comm, ZMod.natCast_eq_zero_iff] at h
    exact h
  have hmod : ∀ m k : ℕ+, (m : ℕ) ∣ (k : ℕ) → v k ≡ v m [MOD (n : ℕ) * m] := by
    intro m k hmk
    have h := proj_eq_val_cast (n := n * m) (k := n * k) (by simpa using Nat.mul_dvd_mul_left _ hmk) x
    have h2 : ((v m : ℕ) : ZMod ((n * m : ℕ+) : ℕ)) = proj (n * m) x := ZMod.natCast_zmod_val _
    rw [← h2, ZMod.natCast_eq_natCast_iff, PNat.mul_coe] at h
    exact h.symm
  let yf : ∀ m : ℕ+, ZMod m := fun m => ((v m / n : ℕ) : ZMod m)
  have hy : yf ∈ profiniteIntegers := by
    rw [mem_profiniteIntegers]
    intro m k hmk
    simp only [yf, map_natCast]
    rw [ZMod.natCast_eq_natCast_iff]
    have h := hmod m k hmk
    obtain ⟨a, ha⟩ := hdvd k
    obtain ⟨b, hb⟩ := hdvd m
    rw [ha, hb] at h ⊢
    rw [Nat.mul_div_cancel_left _ n.pos, Nat.mul_div_cancel_left _ n.pos]
    exact Nat.ModEq.mul_left_cancel' n.ne_zero h
  refine ⟨⟨yf, hy⟩, ?_⟩
  ext m
  rw [map_nsmul, nsmul_eq_mul]
  change proj m x = (n : ZMod m) * ((v m / n : ℕ) : ZMod m)
  rw [← Nat.cast_mul, Nat.mul_div_cancel' (hdvd m)]
  exact proj_eq_val_cast (n := m) (k := n * m) (by simp) x

theorem proj_eq_zero_iff {n : ℕ+} {x : ℤ̂} : proj n x = 0 ↔ x ∈ multiples n := by
  rw [mem_multiples]
  refine ⟨exists_eq_nsmul_of_proj_eq_zero, ?_⟩
  rintro ⟨y, rfl⟩
  rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem ker_proj (n : ℕ+) : (proj n).toAddMonoidHom.ker = multiples n := by
  ext x
  exact proj_eq_zero_iff

theorem eq_zero_of_nsmul_eq_zero {n : ℕ} (hn : n ≠ 0) {x : ℤ̂} (h : n • x = 0) : x = 0 := by
  obtain ⟨N, rfl⟩ : ∃ N : ℕ+, (N : ℕ) = n := ⟨⟨n, Nat.pos_of_ne_zero hn⟩, rfl⟩
  ext m
  rw [map_zero, proj_eq_val_cast (n := m) (k := N * m) (by simp) x, ZMod.natCast_eq_zero_iff]
  have h' := congrArg (proj (N * m)) h
  rw [map_nsmul, map_zero, nsmul_eq_mul] at h'
  have h'' : (((N : ℕ) * (proj (N * m) x).val : ℕ) : ZMod ((N * m : ℕ+) : ℕ)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact h'
  rw [ZMod.natCast_eq_zero_iff] at h''
  have h3 : (N : ℕ) * m ∣ (N : ℕ) * (proj (N * m) x).val := by
    rw [← PNat.mul_coe]
    exact h''
  exact Nat.dvd_of_mul_dvd_mul_left N.pos h3

instance : IsAddTorsionFree ℤ̂ where
  eq_of_nsmul_eq_nsmul_of_addCommute n hn x y _ h := by
    rw [← sub_eq_zero]
    apply eq_zero_of_nsmul_eq_zero hn
    rw [nsmul_sub, h, sub_self]

theorem index_multiples (n : ℕ+) : (multiples n).index = n := by
  rw [← ker_proj, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 (proj_surjective n)]
  simp

theorem eq_multiples_index {H : AddSubgroup ℤ̂} (hH : H.index ≠ 0) : H = multiples H.index := by
  have hle : multiples H.index ≤ H := by
    intro x hx
    obtain ⟨y, rfl⟩ := mem_multiples.1 hx
    exact H.nsmul_index_mem y
  have hidx := AddSubgroup.relIndex_mul_index hle
  have hm := index_multiples ⟨H.index, Nat.pos_of_ne_zero hH⟩
  simp only [PNat.mk_coe] at hm
  rw [hm] at hidx
  have h1 : (multiples H.index).relIndex H = 1 := (Nat.mul_eq_right hH).1 hidx
  exact le_antisymm (AddSubgroup.relIndex_eq_one.1 h1) hle

theorem intCast_mem_multiples_iff {n : ℕ} (hn : 0 < n) {k : ℤ} :
    (k : ℤ̂) ∈ multiples n ↔ (n : ℤ) ∣ k := by
  rw [mem_multiples]
  refine ⟨fun ⟨w, hw⟩ => dvd_of_intCast_eq_nsmul hn hw, ?_⟩
  rintro ⟨c, rfl⟩
  exact ⟨(c : ℤ̂), by push_cast; rw [nsmul_eq_mul]⟩

end ProfiniteInteger

end GroundTheory.LocalField.Abstract
