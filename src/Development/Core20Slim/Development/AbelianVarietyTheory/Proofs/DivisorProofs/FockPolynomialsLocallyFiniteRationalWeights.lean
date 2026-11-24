module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Batteries.Classes.RatCast
public import Formalism.LocalRingCardinality.DataTheta
public import Init.ByCases
public import Init.Classical
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
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
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Order.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockPolGK

theorem X_mul_pderiv_mem {σ : Type} (d : ℕ) (i j : σ) (P : MvPolynomial σ ℂ)
    (hP : P ∈ restrictTotalDegree σ ℂ d) :
    X i * pderiv j P ∈ restrictTotalDegree σ ℂ d := by
  classical
  rw [mem_restrictTotalDegree] at hP
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  have hd : (α.sum fun _ e => e) ≤ d := (le_totalDegree hα).trans hP
  rw [pderiv_monomial]
  by_cases h : α j = 0
  · simp [h]
  · rw [mem_restrictTotalDegree, X, monomial_mul]
    refine (totalDegree_monomial_le _ _).trans (le_trans (le_of_eq ?_) hd)
    have hα : α = Finsupp.single j 1 + (α - Finsupp.single j 1) := by
      ext k
      by_cases hk : k = j
      · subst hk; simp; omega
      · simp [hk]
    conv_rhs => rw [hα]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp
    rfl

theorem omE_mem {p q r s : ℕ} (d : ℕ) (l l' : Ln p q r s) (h : linePos l = linePos l')
    (P : Pol p q r s) (hP : P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d) :
    omE l l' P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d := by
  unfold omE
  rw [LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · cases hl : linePos l
    · have hl' : linePos l' = false := h ▸ hl
      simp only [raiB, lowB, hl, hl', Bool.false_eq_true, if_false]
      change -(pderiv l ((X l' : Pol p q r s) * P)) ∈ _
      refine Submodule.neg_mem _ ?_
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Submodule.add_mem _ (X_mul_pderiv_mem d _ _ P hP) ?_
      by_cases e : l' = l
      · subst e; rw [pderiv_X_self, mul_one]; exact hP
      · rw [pderiv_X_of_ne e, mul_zero]; exact Submodule.zero_mem _
    · have hl' : linePos l' = true := h ▸ hl
      simp only [raiB, lowB, hl, hl', if_true]
      exact X_mul_pderiv_mem d _ _ P hP
  · split_ifs
    · exact Submodule.smul_mem _ _ hP
    · exact Submodule.zero_mem _

theorem omAct_mem {p q r s : ℕ} (d : ℕ) (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ)
    (hZ : ∀ l l', linePos l ≠ linePos l' → Z l l' = 0)
    (P : Pol p q r s) (hP : P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d) :
    omAct p q r s Z P ∈ restrictTotalDegree (Ix p q × Ix r s) ℂ d := by
  rw [omAct_apply, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l' _ => ?_
  rw [LinearMap.smul_apply]
  by_cases h : linePos l = linePos l'
  · exact Submodule.smul_mem _ _ (omE_mem d l l' h P hP)
  · rw [hZ l l' h, zero_smul]; exact Submodule.zero_mem _

theorem kStable1 (p q r s d : ℕ) :
    KStable (fockAct1 p q r s) (restrictTotalDegree (Ix p q × Ix r s) ℂ d) := by
  intro Z hZ P hP
  refine omAct_mem d _ ?_ P hP
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  change Z a b * (1 : Mat r s) c e = 0
  by_cases hc : c = e
  · subst hc
    rw [hZ a b, zero_mul]
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp_all [linePos, sameBlock]
  · rw [Matrix.one_apply_ne hc, mul_zero]

theorem kStable2 (p q r s d : ℕ) :
    KStable (fockAct2 p q r s) (restrictTotalDegree (Ix p q × Ix r s) ℂ d) := by
  intro Z hZ P hP
  refine omAct_mem d _ ?_ P hP
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  change (1 : Mat p q) a b * Z c e = 0
  by_cases hc : a = b
  · subst hc
    rw [hZ c e, mul_zero]
    rcases a with a | a <;> rcases c with c | c <;> rcases e with e | e <;>
      simp_all [linePos, sameBlock]
  · rw [Matrix.one_apply_ne hc, zero_mul]

def signQ {p q r s : ℕ} (a : Ix p q) (c : Ix r s) : ℚ := if linePos (a, c) then 1 else -1

theorem cast_signQ {p q r s : ℕ} (a : Ix p q) (c : Ix r s) :
    ((signQ a c : ℚ) : ℂ) = lineSign a c := by
  rcases a with a | a <;> rcases c with c | c <;> simp [signQ, linePos, lineSign]

theorem mem_of_monomials {σ : Type} (N : Submodule ℂ (MvPolynomial σ ℂ))
    (h : ∀ α, monomial α (1 : ℂ) ∈ N) (P : MvPolynomial σ ℂ) : P ∈ N := by
  rw [P.as_sum]
  refine Submodule.sum_mem _ fun α _ => ?_
  have := N.smul_mem (AddMonoidAlgebra.coeff P α) (h α)
  rwa [smul_monomial, smul_eq_mul, mul_one] at this

theorem monomial_mem_weightSpace_fockAction_first {p q r s : ℕ} (α : Ln p q r s →₀ ℕ) :
    (monomial α 1 : Pol p q r s) ∈ wtSub (fockAct1 p q r s)
      (fun a => ∑ c, signQ a c * ((α (a, c) : ℚ) + 1 / 2)) := by
  unfold wtSub
  rw [Submodule.mem_iInf]
  intro a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, cartan1, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  congr 1
  push_cast
  simp only [cast_signQ]

theorem monomial_mem_weightSpace_fockAction_second {p q r s : ℕ} (α : Ln p q r s →₀ ℕ) :
    (monomial α 1 : Pol p q r s) ∈ wtSub (fockAct2 p q r s)
      (fun c => ∑ a, signQ a c * ((α (a, c) : ℚ) + 1 / 2)) := by
  unfold wtSub
  rw [Submodule.mem_iInf]
  intro a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, cartan2, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  congr 1
  push_cast
  simp only [cast_signQ]

theorem pol_locFin_weights : ∀ (p q r s : ℕ), (∀ P : Pol p q r s, (∃ W : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ W ∧ P ∈ W ∧ KStable (fockAct1 p q r s) W) ∧ P ∈ ⨆ μ : Ix p q → ℚ, wtSub (fockAct1 p q r s) μ) ∧ (∀ P : Pol p q r s, (∃ W : Submodule ℂ (Pol p q r s), FiniteDimensional ℂ W ∧ P ∈ W ∧ KStable (fockAct2 p q r s) W) ∧ P ∈ ⨆ μ : Ix r s → ℚ, wtSub (fockAct2 p q r s) μ) := by
  intro p q r s
  refine ⟨fun P => ⟨⟨restrictTotalDegree _ ℂ P.totalDegree, inferInstance, ?_, kStable1 _ _ _ _ _⟩, ?_⟩,
    fun P => ⟨⟨restrictTotalDegree _ ℂ P.totalDegree, inferInstance, ?_, kStable2 _ _ _ _ _⟩, ?_⟩⟩
  · rw [mem_restrictTotalDegree]
  · exact mem_of_monomials _ (fun α => Submodule.mem_iSup_of_mem _ (monomial_mem_weightSpace_fockAction_first α)) P
  · rw [mem_restrictTotalDegree]
  · exact mem_of_monomials _ (fun α => Submodule.mem_iSup_of_mem _ (monomial_mem_weightSpace_fockAction_second α)) P

end GlobalTheory.FockPolGK
