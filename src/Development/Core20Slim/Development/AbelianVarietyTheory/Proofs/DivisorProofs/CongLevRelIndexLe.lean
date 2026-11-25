module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleMod
public import Batteries.Logic
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.CongIdx

variable {D : D7}

theorem inc_int_mem (a : 𝓞 D.host.E) : inc D (a : D.host.E) ∈ OhE D :=
  Subring.subset_closure (Or.inl ⟨⟨(a : D.host.E), ⟨a, rfl⟩⟩, rfl⟩)

theorem mul_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {t y : AE D} (ht : t ∈ OhE D) (hy : y ∈ hatId D 𝔪) :
    t * y ∈ hatId D 𝔪 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, s * t, mul_mem hs ht, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem ohE_approx (N : ℕ) (hN : 1 ≤ N) (x : AE D) (hx : x ∈ OhE D) :
    ∃ a ∈ Formalism.UG.intOE D.host.E, ∃ z ∈ OhE D, x = inc D a + (N : AE D) * z := by
  first
  | exact @_root_.GlobalTheory.AdeleTensorModule.main
  | exact _root_.GlobalTheory.AdeleTensorModule.main
  | (apply _root_.GlobalTheory.AdeleTensorModule.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdeleTensorModule.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdeleTensorModule.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdeleTensorModule.main ..)

theorem exists_rep {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {x : AE D} (hx : x ∈ OhE D) :
    ∃ a : 𝓞 D.host.E, x - inc D (a : D.host.E) ∈ hatId D 𝔪 := by
  have hN : 1 ≤ Ideal.absNorm 𝔪 := Nat.one_le_iff_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  obtain ⟨a0, ⟨a, rfl⟩, z, hz, e⟩ := ohE_approx _ hN x hx
  refine ⟨a, ?_⟩
  have e2 : x - inc D (algebraMap (𝓞 D.host.E) D.host.E a) = (Ideal.absNorm 𝔪 : AE D) * z := by
    rw [e]; ring
  have e3 : inc D (((Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E) : D.host.E) = (Ideal.absNorm 𝔪 : AE D) := by
    simp
  rw [show ((a : D.host.E)) = algebraMap (𝓞 D.host.E) D.host.E a from rfl, e2, ← e3]
  exact AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem 𝔪, z, hz, rfl⟩

theorem inv_mul_mem {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {k k' : GA D N} (hk : k ∈ intG D N) (hk' : k' ∈ intG D N)
    (h : ∀ i j, ((k' : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
      ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ hatId D 𝔪) :
    k⁻¹ * k' ∈ congLev D 𝔪 N := by
  refine Subgroup.subset_closure ⟨mul_mem (inv_mem hk) hk', fun i j => ?_⟩
  have hi := (mem_intG k).1 hk
  have e : (((k⁻¹ * k' : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1 =
      (((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        (((k' : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) -
          ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) := by
    rw [Matrix.mul_sub, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rfl
  rw [e, Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem_hatId (hi i l).2 (h l j)

end GlobalTheory.CongIdx


open GlobalTheory.CongIdx in
theorem GlobalTheory.congLev_relIndex_le : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ N : ℕ,
    (congLev D 𝔪 N).relIndex (intG D N) ≠ 0 ∧ (congLev D 𝔪 N).relIndex (intG D N) ≤ Ideal.absNorm 𝔪 ^ (N ^ 2) := by
  intro D 𝔪 h𝔪 N
  classical
  have hrep : ∀ x : AE D, ∃ a : 𝓞 D.host.E, x ∈ OhE D → x - inc D (a : D.host.E) ∈ hatId D 𝔪 := fun x => by
    by_cases hx : x ∈ OhE D
    · obtain ⟨a, ha⟩ := exists_rep h𝔪 hx
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose r hr using hrep
  let f : intG D N → (Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪) := fun k i j =>
    Ideal.Quotient.mk 𝔪 (r ((((k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j))
  let g : intG D N ⧸ (congLev D 𝔪 N).subgroupOf (intG D N) → (Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪) :=
    fun q => f q.out
  have hg : Function.Injective g := by
    intro q1 q2 h
    rw [← QuotientGroup.out_eq' q1, ← QuotientGroup.out_eq' q2, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hk := (q1.out).2
    have hk' := (q2.out).2
    refine (show ((q1.out⁻¹ * q2.out : intG D N) : GA D N) = (q1.out : GA D N)⁻¹ * q2.out from rfl) ▸
      inv_mul_mem hk hk' fun i j => ?_
    have h1 := hr _ ((mem_intG _).1 hk i j).1
    have h2 := hr _ ((mem_intG _).1 hk' i j).1
    have h3 : r ((((q2.out : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j) -
        r ((((q1.out : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j) ∈ 𝔪 :=
      Ideal.Quotient.eq.1 (congr_fun (congr_fun h i) j).symm
    have h4 : inc D (((r ((((q2.out : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j) -
        r ((((q1.out : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j) : 𝓞 D.host.E) : D.host.E)) * 1 ∈
        hatId D 𝔪 := AddSubgroup.subset_closure ⟨_, h3, 1, one_mem _, rfl⟩
    have h5 := add_mem (sub_mem h2 h1) h4
    convert h5 using 1
    push_cast
    simp only [map_sub, mul_one]
    ring
  have hfin : Ideal.absNorm 𝔪 ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 h𝔪
  have hcard : Nat.card (𝓞 D.host.E ⧸ 𝔪) = Ideal.absNorm 𝔪 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.host.E ⧸ 𝔪) := Nat.finite_of_card_ne_zero (hcard ▸ hfin)
  haveI : Finite (intG D N ⧸ (congLev D 𝔪 N).subgroupOf (intG D N)) := Finite.of_injective g hg
  have hle := Nat.card_le_card_of_injective g hg
  rw [Nat.card_fun, Nat.card_fun, hcard, Nat.card_fin, ← pow_mul] at hle
  refine ⟨?_, ?_⟩
  · exact Subgroup.index_ne_zero_of_finite
  · calc (congLev D 𝔪 N).relIndex (intG D N) = Nat.card (intG D N ⧸ (congLev D 𝔪 N).subgroupOf (intG D N)) := rfl
      _ ≤ _ := hle
      _ = _ := by rw [sq]
