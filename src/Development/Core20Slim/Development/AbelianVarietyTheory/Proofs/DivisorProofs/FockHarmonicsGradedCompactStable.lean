module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommuteStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineKroneckerRightMatrixConjTranspose
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.Lattice.Lemmas
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.Nat
public import Mathlib.Order.SetNotation
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg.HarmStable

section General

variable {σ : Type}

def DegZero (K : Module.End ℂ (MvPolynomial σ ℂ)) : Prop :=
  ∀ (d : ℕ) (P : MvPolynomial σ ℂ), P ∈ homog σ d → K P ∈ homog σ d

theorem hc_hc (d e : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent d (homogeneousComponent e P) =
      if d = e then homogeneousComponent e P else 0 :=
  homogeneousComponent_of_mem (homogeneousComponent_mem e P)

theorem DegZero.comm {K : Module.End ℂ (MvPolynomial σ ℂ)} (hK : DegZero K) (d : ℕ)
    (P : MvPolynomial σ ℂ) : homogeneousComponent d (K P) = K (homogeneousComponent d P) := by
  rw [← sum_homogeneousComponent P]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [homogeneousComponent_of_mem (hK e _ (homogeneousComponent_mem e P)), hc_hc]
  split_ifs <;> simp

theorem minusPart_eq_zero_iff (A : Module.End ℂ (MvPolynomial σ ℂ)) (P : MvPolynomial σ ℂ) :
    minusPart A P = 0 ↔
      ∀ d, homogeneousComponent d (A (homogeneousComponent (d + 2) P)) = 0 := by
  constructor
  · intro h d
    have hfin : (Function.support fun e : ℕ =>
        homogeneousComponent e (A (homogeneousComponent (e + 2) P))) ⊆
        ((Finset.range (P.totalDegree + 1) ∪ {d} : Finset ℕ) : Set ℕ) := by
      intro e he
      by_contra hne
      apply he
      have : P.totalDegree < e + 2 := by
        simp only [Finset.coe_union, Finset.coe_range, Set.mem_union, Set.mem_Iio, not_or] at hne
        omega
      simp [homogeneousComponent_eq_zero _ _ this]
    rw [minusPart, finsum_eq_sum_of_support_subset _ hfin] at h
    have h2 := congrArg (homogeneousComponent d) h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h2
    simp only [hc_hc] at h2
    rw [Finset.sum_ite_eq] at h2
    simpa using h2
  · intro h
    rw [minusPart]
    simp [h]

def lowKer {ι : Type} (A : ι → Module.End ℂ (MvPolynomial σ ℂ)) (c : ι → Prop) :
    Submodule ℂ (MvPolynomial σ ℂ) :=
  ⨅ Z, ⨅ (_ : c Z), ⨅ d : ℕ,
    LinearMap.ker (homogeneousComponent d ∘ₗ A Z ∘ₗ homogeneousComponent (d + 2))

theorem mem_lowKer {ι : Type} {A : ι → Module.End ℂ (MvPolynomial σ ℂ)} {c : ι → Prop}
    {P : MvPolynomial σ ℂ} : P ∈ lowKer A c ↔
      ∀ Z, c Z → ∀ d, homogeneousComponent d (A Z (homogeneousComponent (d + 2) P)) = 0 := by
  simp [lowKer, Submodule.mem_iInf]

theorem coe_lowKer {ι : Type} (A : ι → Module.End ℂ (MvPolynomial σ ℂ)) (c : ι → Prop) :
    (lowKer A c : Set (MvPolynomial σ ℂ)) = {P | ∀ Z, c Z → minusPart (A Z) P = 0} := by
  ext P
  simp only [SetLike.mem_coe, mem_lowKer, Set.mem_setOf_eq, minusPart_eq_zero_iff]

theorem hc_mem_lowKer {ι : Type} {A : ι → Module.End ℂ (MvPolynomial σ ℂ)} {c : ι → Prop}
    {P : MvPolynomial σ ℂ} (hP : P ∈ lowKer A c) (e : ℕ) :
    homogeneousComponent e P ∈ lowKer A c := by
  rw [mem_lowKer] at hP ⊢
  intro Z hZ d
  rw [hc_hc]
  split_ifs with h
  · rw [← h]; exact hP Z hZ d
  · simp

theorem map_mem_lowKer {ι : Type} {A : ι → Module.End ℂ (MvPolynomial σ ℂ)} {c : ι → Prop}
    {K : Module.End ℂ (MvPolynomial σ ℂ)} (hK : DegZero K)
    (hc : ∀ Z, c Z → A Z * K = K * A Z ∨ ∃ Z', c Z' ∧ A Z' = A Z * K - K * A Z)
    {P : MvPolynomial σ ℂ} (hP : P ∈ lowKer A c) : K P ∈ lowKer A c := by
  rw [mem_lowKer] at hP ⊢
  intro Z hZ d
  rw [hK.comm, ← Module.End.mul_apply (A Z) K]
  rcases hc Z hZ with h | ⟨Z', hZ', h⟩
  · rw [h, Module.End.mul_apply, hK.comm, hP Z hZ d, map_zero]
  · rw [← sub_add_cancel (A Z * K) (K * A Z), ← h, LinearMap.add_apply, map_add (f := _), hP Z' hZ' d,
      Module.End.mul_apply, hK.comm, hP Z hZ d, map_zero, add_zero]

theorem X_mul_pderiv_mem (u v : σ) {d : ℕ} {P : MvPolynomial σ ℂ} (hP : P ∈ homog σ d) :
    X u * pderiv v P ∈ homog σ d := by
  rcases d with _ | d
  · rw [totalDegree_eq_zero_iff_eq_C.1 ((totalDegree_zero_iff_isHomogeneous _).2 hP), pderiv_C,
      mul_zero]
    exact Submodule.zero_mem _
  · have := (isHomogeneous_X ℂ u).mul (IsHomogeneous.pderiv (i := v) hP)
    rwa [Nat.add_sub_cancel, add_comm] at this

theorem pderiv_X_mul_mem (u v : σ) {d : ℕ} {P : MvPolynomial σ ℂ} (hP : P ∈ homog σ d) :
    pderiv v (X u * P) ∈ homog σ d := by
  have := IsHomogeneous.pderiv (i := v) ((isHomogeneous_X ℂ u).mul hP)
  rwa [Nat.add_sub_cancel_left] at this

end General

variable {p q r s : ℕ}

theorem degZero_omE {l l' : Ln p q r s} (h : linePos l = linePos l') : DegZero (omE l l') := by
  intro d P hP
  rw [omE, LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · rw [raiB, lowB, ← h]
    split_ifs
    · exact X_mul_pderiv_mem l l' hP
    · exact Submodule.neg_mem _ (pderiv_X_mul_mem l' l hP)
  · split_ifs
    · exact Submodule.smul_mem _ _ hP
    · exact Submodule.zero_mem _

theorem degZero_omAct {M : Matrix (Ln p q r s) (Ln p q r s) ℂ}
    (h : ∀ l l', linePos l ≠ linePos l' → M l l' = 0) : DegZero (omAct p q r s M) := by
  intro d P hP
  rw [omAct_apply, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l' _ => ?_
  by_cases hl : linePos l = linePos l'
  · exact Submodule.smul_mem _ _ (degZero_omE hl d P hP)
  · rw [h l l' hl, zero_smul]; exact Submodule.zero_mem _

theorem degZero_fockAct1 {Y : Mat p q} (hY : IsKC Y) : DegZero (fockAct1 p q r s Y) := by
  refine degZero_omAct ?_
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  show Y a b * (1 : Mat r s) c e = 0
  by_cases hce : c = e
  · subst hce
    rw [hY a b, zero_mul]
    revert h
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp [linePos, sameBlock]
  · rw [Matrix.one_apply_ne hce, mul_zero]

theorem degZero_fockAct2 {Y : Mat r s} (hY : IsKC Y) : DegZero (fockAct2 p q r s Y) := by
  refine degZero_omAct ?_
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  show (1 : Mat p q) a b * Y c e = 0
  by_cases hab : a = b
  · subst hab
    rw [hY c e, mul_zero]
    revert h
    rcases a with a | a <;> rcases e with e | e <;> rcases c with c | c <;>
      simp [linePos, sameBlock]
  · rw [Matrix.one_apply_ne hab, zero_mul]

theorem isPC_bracket {Y Z : Mat p q} (hY : IsKC Y) (hZ : IsPC Z) : IsPC (Z * Y - Y * Z) := by
  intro a b hab
  have h1 : (Z * Y) a b = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : sameBlock a c
    · rw [hZ a c hc, zero_mul]
    · rw [hY c b, mul_zero]
      revert hab hc
      rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp [sameBlock]
  have h2 : (Y * Z) a b = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : sameBlock a c
    · rw [hZ c b, mul_zero]
      revert hab hc
      rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp [sameBlock]
    · rw [hY a c hc, zero_mul]
  rw [Matrix.sub_apply, h1, h2, sub_zero]

def sub1 (p q r s : ℕ) : Submodule ℂ (Pol p q r s) :=
  lowKer (fun Z : Mat r s => fockAct2 p q r s Z) IsPC

def sub2 (p q r s : ℕ) : Submodule ℂ (Pol p q r s) :=
  lowKer (fun Z : Mat p q => fockAct1 p q r s Z) IsPC

theorem coe_fockHarmonicsFirstMemberSubspace : (sub1 p q r s : Set (Pol p q r s)) = harm1 p q r s := coe_lowKer _ _

theorem coe_fockHarmonicsSecondMemberSubmodule : (sub2 p q r s : Set (Pol p q r s)) = harm2 p q r s := coe_lowKer _ _

theorem fockHarmonicsFirstMember_kStable : KStable (fockAct1 p q r s) (sub1 p q r s) ∧
    KStable (fockAct2 p q r s) (sub1 p q r s) := by
  obtain ⟨-, -, h2, h3⟩ := GlobalTheory.T.fockOperators_lie_representation_commute p q r s
  exact ⟨fun Y hY _ hw => map_mem_lowKer (degZero_fockAct1 hY)
      (fun Z _ => Or.inl (h3 Y Z).symm) hw,
    fun Y hY _ hw => map_mem_lowKer (degZero_fockAct2 hY)
      (fun Z hZ => Or.inr ⟨_, isPC_bracket hY hZ, h2 Z Y⟩) hw⟩

theorem fockHarmonicsSecondMember_kStable : KStable (fockAct1 p q r s) (sub2 p q r s) ∧
    KStable (fockAct2 p q r s) (sub2 p q r s) := by
  obtain ⟨-, h1, -, h3⟩ := GlobalTheory.T.fockOperators_lie_representation_commute p q r s
  exact ⟨fun Y hY _ hw => map_mem_lowKer (degZero_fockAct1 hY)
      (fun Z hZ => Or.inr ⟨_, isPC_bracket hY hZ, h1 Z Y⟩) hw,
    fun Y hY _ hw => map_mem_lowKer (degZero_fockAct2 hY)
      (fun Z _ => Or.inl (h3 Z Y)) hw⟩

end GlobalTheory.FockAlg.HarmStable

namespace GlobalTheory.FockAlg

open HarmStable

theorem harm_graded_stable : ∀ (p q r s : ℕ) (S : Set (Pol p q r s)),
    (S = harm1 p q r s ∨ S = harm2 p q r s ∨ S = jointHarm p q r s) →
    (Submodule.span ℂ S : Set (Pol p q r s)) = S ∧
      KStable (fockAct1 p q r s) (Submodule.span ℂ S) ∧
      KStable (fockAct2 p q r s) (Submodule.span ℂ S) ∧
      ∀ P ∈ S, ∀ d : ℕ, homogeneousComponent d P ∈ S := by
  intro p q r s S hS
  rcases hS with rfl | rfl | rfl
  · rw [← coe_fockHarmonicsFirstMemberSubspace, Submodule.span_eq]
    exact ⟨rfl, fockHarmonicsFirstMember_kStable.1, fockHarmonicsFirstMember_kStable.2, fun P hP d => hc_mem_lowKer hP d⟩
  · rw [← coe_fockHarmonicsSecondMemberSubmodule, Submodule.span_eq]
    exact ⟨rfl, fockHarmonicsSecondMember_kStable.1, fockHarmonicsSecondMember_kStable.2, fun P hP d => hc_mem_lowKer hP d⟩
  · rw [jointHarm, ← coe_fockHarmonicsFirstMemberSubspace, ← coe_fockHarmonicsSecondMemberSubmodule, ← Submodule.coe_inf, Submodule.span_eq]
    exact ⟨rfl,
      fun Y hY w hw => ⟨fockHarmonicsSecondMember_kStable.1 Y hY w hw.1, fockHarmonicsFirstMember_kStable.1 Y hY w hw.2⟩,
      fun Y hY w hw => ⟨fockHarmonicsSecondMember_kStable.2 Y hY w hw.1, fockHarmonicsFirstMember_kStable.2 Y hY w hw.2⟩,
      fun P hP d => ⟨hc_mem_lowKer hP.1 d, hc_mem_lowKer hP.2 d⟩⟩

end GlobalTheory.FockAlg
