module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Nat.Div.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.LocIndex

theorem index_coprime_of_multiples {G : Type*} [AddCommGroup G] [AddGroup.FG G] (H : AddSubgroup G) (p : ℕ)
    (hp : p.Prime) (h : ∀ z : G, ∃ s : ℕ, Nat.Coprime s p ∧ s • z ∈ H) : Nat.Coprime H.index p := by
  have hq : ∀ x : G ⧸ H, ∃ s : ℕ, Nat.Coprime s p ∧ s • x = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨s, hs, hz⟩ := h z
    refine ⟨s, hs, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact hz
  have htor : AddMonoid.IsTorsion (G ⧸ H) := by
    intro x
    obtain ⟨s, hs, hx⟩ := hq x
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨s, Nat.pos_of_ne_zero ?_, hx⟩
    rintro rfl
    exact hp.one_lt.ne' (by simpa using hs)
  haveI : Finite (G ⧸ H) := AddCommGroup.finite_of_fg_torsion _ htor
  haveI := Fact.mk hp
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := G ⧸ H) p hd
  obtain ⟨s, hs, hs0⟩ := hq x
  have : p ∣ s := hx ▸ addOrderOf_dvd_of_nsmul_eq_zero hs0
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hs.symm this

theorem mul_mem_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a : 𝓞 D.host.K) {w : ℂ}
    (hw : w ∈ lamOf D cc δ) : w * D.host.φ₀ ((a : D.host.K) : D.host.E) ∈ lamOf D cc δ := by
  unfold lamOf at hw
  induction hw using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨c * a, cc.mul_mem_right a hc, ?_⟩
    rw [mul_assoc, ← map_mul]
    congr 2
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem exists_multiple_mem (D : D7) (hD : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (p : ℕ) (hb : LocBasis D p (YYl D L L') b)
    (z : VC D N N') (hz : z ∈ La D (tor0 D cc δ) L L') :
    ∃ s : ℕ, Nat.Coprime s p ∧ s • z ∈ LaB D (tor0 D cc δ) b := by
  unfold La at hz
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    obtain ⟨s, hs, c, hc⟩ := hb.2.2 A hA
    refine ⟨s, hs, ?_⟩
    have key : s • w • embV D (tor0 D cc δ) A =
        ∑ i, (w * D.host.φ₀ ((c i : D.host.K) : D.host.E)) • embV D (tor0 D cc δ) (b i) := by
      funext τ i j
      have h1 := congrArg (fun M => embT D τ (M i j)) hc
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast, Matrix.sum_apply, map_sum] at h1
      simp only [hD.1 τ] at h1
      simp only [Pi.smul_apply, Finset.sum_apply, embV, tor0, smul_eq_mul, nsmul_eq_mul]
      rw [mul_left_comm, h1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [key]
    exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨_, mul_mem_lamOf D cc δ (c i) hw, i, rfl⟩
  | zero => exact ⟨1, Nat.coprime_one_left p, by rw [smul_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨t, ht, hy⟩ := hy
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx t
    · rw [mul_smul]; exact nsmul_mem hy s
  | neg x _ hx =>
    obtain ⟨s, hs, hx⟩ := hx
    exact ⟨s, hs, by rw [smul_neg]; exact neg_mem hx⟩

theorem index_coprime : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (p : ℕ), p.Prime → (La D (tor0 D cc δ) L L').FG → LocBasis D p (YYl D L L') b → Nat.Coprime (((LaB D (tor0 D cc δ) b).addSubgroupOf (La D (tor0 D cc δ) L L')).index) p := by
  intro D hD cc δ N N' r L L' b p hp hfg hb
  haveI : AddGroup.FG (La D (tor0 D cc δ) L L') := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
  refine index_coprime_of_multiples _ p hp fun z => ?_
  obtain ⟨s, hs, hz⟩ := exists_multiple_mem D hD cc δ L L' b p hb z.1 z.2
  exact ⟨s, hs, AddSubgroup.mem_addSubgroupOf.2 hz⟩

end GlobalTheory.NormSum.LocIndex
