module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
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
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.CongReps

variable (D : D7) (𝔪 : Ideal (𝓞 D.host.E))


variable {D 𝔪} in
theorem mul_mem_hatId {t x : AE D} (ht : t ∈ OhE D) (hx : x ∈ hatId D 𝔪) : t * x ∈ hatId D 𝔪 := by
  unfold hatId at hx ⊢
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, t * s, mul_mem ht hs, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
  | neg y _ hy => rw [mul_neg]; exact neg_mem hy


variable {D 𝔪} in
theorem inc_sub_mem {r r' : 𝓞 D.host.E} (h : r - r' ∈ 𝔪) :
    inc D (r : D.host.E) - inc D (r' : D.host.E) ∈ hatId D 𝔪 :=
  AddSubgroup.subset_closure ⟨r - r', h, 1, one_mem _, by push_cast; rw [map_sub, mul_one]⟩


variable {D 𝔪} in
theorem exists_rep (h𝔪 : 𝔪 ≠ ⊥) {s : AE D} (hs : s ∈ OhE D) :
    ∃ r : 𝓞 D.host.E, s - inc D (r : D.host.E) ∈ hatId D 𝔪 := by
  have hn : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  obtain ⟨r, hr, w, hw, e⟩ := GlobalTheory.HeckeVal.exists_approx D _ hn s hs
  refine ⟨⟨r, hr⟩, AddSubgroup.subset_closure ⟨(Ideal.absNorm 𝔪 : 𝓞 D.host.E), Ideal.absNorm_mem 𝔪, w, hw, ?_⟩⟩
  rw [e]
  change inc D r + (Ideal.absNorm 𝔪 : AE D) * w - inc D r = inc D (((Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E) : D.host.E) * w
  simp

def congRel (N : ℕ) : Setoid {k : GA D N // k ∈ intG D N} where
  r k k' := ∀ i j, ((k.1 : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
    ((k'.1 : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ hatId D 𝔪
  iseqv := by
    refine ⟨fun k i j => by rw [sub_self]; exact zero_mem _, fun h i j => by rw [← neg_sub]; exact neg_mem (h i j),
      fun h h' i j => ?_⟩
    have := add_mem (h i j) (h' i j)
    rwa [sub_add_sub_cancel] at this


variable {D 𝔪} in
theorem congOne_inv_mul_iff {N : ℕ} {r : GA D N} (hr : r ∈ intG D N) (k : GA D N) :
    CongOne D 𝔪 (r⁻¹ * k) ↔ ∀ i j, ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
      ((r : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ hatId D 𝔪 := by
  have hI := (mem_intG r).1 hr
  set Rm : Matrix (Fin N) (Fin N) (AE D) := ((r : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
  set Ri : Matrix (Fin N) (Fin N) (AE D) := (((r : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
  set K : Matrix (Fin N) (Fin N) (AE D) := ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
  have e0 : (((r⁻¹ * k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = Ri * K := by
    simp [Rm, Ri, K]
  have e1 : Ri * K - 1 = Ri * (K - Rm) := by
    rw [Matrix.mul_sub]
    congr 1
    exact (Units.inv_mul (r : GL (Fin N) (AE D))).symm
  have e2 : K - Rm = Rm * (Ri * K - 1) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.mul_one]
    congr 1
    rw [show Rm * Ri = 1 from Units.mul_inv (r : GL (Fin N) (AE D)), Matrix.one_mul]
  unfold CongOne
  rw [e0]
  constructor
  · intro h i j
    rw [← Matrix.sub_apply, e2, Matrix.mul_apply]
    exact sum_mem fun l _ => mul_mem_hatId (hI i l).1 (h l j)
  · intro h i j
    rw [e1, Matrix.mul_apply]
    exact sum_mem fun l _ => mul_mem_hatId (hI i l).2 (by rw [Matrix.sub_apply]; exact h l j)


open Classical in
def red (x : AE D) : 𝓞 D.host.E ⧸ 𝔪 :=
  if h : ∃ r : 𝓞 D.host.E, x - inc D (r : D.host.E) ∈ hatId D 𝔪 then Ideal.Quotient.mk 𝔪 h.choose else 0


variable {D 𝔪} in
theorem sub_mem_of_red_eq (h𝔪 : 𝔪 ≠ ⊥) {x y : AE D} (hx : x ∈ OhE D) (hy : y ∈ OhE D) (h : red D 𝔪 x = red D 𝔪 y) :
    x - y ∈ hatId D 𝔪 := by
  have ex := exists_rep h𝔪 hx
  have ey := exists_rep h𝔪 hy
  unfold red at h
  rw [dite_eq_left ex, dite_eq_left ey, Ideal.Quotient.eq] at h
  have := add_mem (sub_mem ex.choose_spec ey.choose_spec) (inc_sub_mem h)
  convert this using 1
  ring

theorem finite_congRel (h𝔪 : 𝔪 ≠ ⊥) (N : ℕ) : Finite (Quotient (congRel D 𝔪 N)) := by
  haveI : Finite (𝓞 D.host.E ⧸ 𝔪) := Ideal.finiteQuotientOfFreeOfNeBot 𝔪 h𝔪
  let φ : {k : GA D N // k ∈ intG D N} → Fin N → Fin N → 𝓞 D.host.E ⧸ 𝔪 := fun k i j =>
    red D 𝔪 (((k.1 : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j)
  let g : {q // ∃ k, φ k = q} → Quotient (congRel D 𝔪 N) := fun q => Quotient.mk _ q.2.choose
  refine Finite.of_surjective g fun c => ?_
  induction c using Quotient.inductionOn with
  | h k =>
    refine ⟨⟨φ k, k, rfl⟩, Quotient.sound fun i j => ?_⟩
    have hq : φ (⟨φ k, k, rfl⟩ : {q // ∃ k, φ k = q}).2.choose = φ k := (⟨φ k, k, rfl⟩ : {q // ∃ k, φ k = q}).2.choose_spec
    set k' := (⟨φ k, k, rfl⟩ : {q // ∃ k, φ k = q}).2.choose
    exact sub_mem_of_red_eq h𝔪 (((mem_intG k'.1).1 k'.2) i j).1 (((mem_intG k.1).1 k.2) i j).1
      (congrFun (congrFun hq i) j)

theorem exists_reps : ∀ (D : D7) (N : ℕ) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∃ R : Finset (GA D N),
    (∀ r ∈ R, r ∈ intG D N) ∧ ∀ k ∈ intG D N, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k) := by
  intro D N 𝔪 h𝔪
  haveI := finite_congRel D 𝔪 h𝔪 N
  haveI : Fintype (Quotient (congRel D 𝔪 N)) := Fintype.ofFinite _
  classical
  refine ⟨Finset.univ.image fun c : Quotient (congRel D 𝔪 N) => c.out.1, ?_, ?_⟩
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    exact c.out.2
  · intro k hk
    let c := Quotient.mk (congRel D 𝔪 N) ⟨k, hk⟩
    refine ⟨c.out.1, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ c), ?_⟩, ?_⟩
    · rw [congOne_inv_mul_iff c.out.2]
      have := Quotient.exact (Quotient.out_eq c)
      intro i j
      have h := (congRel D 𝔪 N).iseqv.symm this i j
      exact h
    · rintro r ⟨hr, hc⟩
      obtain ⟨c', -, rfl⟩ := Finset.mem_image.1 hr
      rw [congOne_inv_mul_iff c'.out.2] at hc
      have h1 : (congRel D 𝔪 N) c'.out ⟨k, hk⟩ := (congRel D 𝔪 N).iseqv.symm hc
      have h3 : c' = c := by
        rw [← Quotient.out_eq c']
        exact Quotient.sound h1
      rw [h3]

end GlobalTheory.CongReps

end
