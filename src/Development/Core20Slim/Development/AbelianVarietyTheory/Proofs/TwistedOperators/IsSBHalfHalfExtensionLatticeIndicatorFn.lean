module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.CosetRow.ExtSB

variable {D : D7} {m n : ℕ}

theorem half_of_idem' {b : AE D} (hb : b * b = b) (t : Mx D m n) : IsHalf b (b • t) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  linear_combination (t i j) * hb

theorem half_add_nsmul_iff {e : AE D} {t u : Mx D m n} (hu : IsHalf e u) (k : ℕ) :
    IsHalf e (t + k • u) ↔ IsHalf e t := by
  constructor
  · intro h i j
    have h1 := h i j
    have h2 := hu i j
    simp only [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul] at h1
    linear_combination h1 - (k : AE D) * h2
  · intro h i j
    have h1 := h i j
    have h2 := hu i j
    simp only [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
    linear_combination h1 + (k : AE D) * h2

theorem smul_add_nsmul (e : AE D) (t u : Mx D m n) (k : ℕ) : e • (t + k • u) = e • t + k • (e • u) := by
  rw [smul_add, smul_comm]

theorem isSBHalf_extFn : ∀ {D : D7} {m n : ℕ} {Λ : AddSubgroup (Mx D m n)} {e₀ e₁ : AE D} {Φ : Mx D m n → ℂ}, e₀ * e₀ = e₀ → e₁ * e₁ = e₁ → e₀ * e₁ = 0 → (∀ u ∈ Λ, e₀ • u ∈ Λ) → (∀ u ∈ Λ, e₁ • u ∈ Λ) → IsSBHalf e₀ Λ Φ → IsSBHalf (e₀ + e₁) Λ (GlobalTheory.CosetRow.extFn e₀ e₁ Λ Φ) := by
  intro D m n Λ e₀ e₁ Φ h0 h1 h01 hΛ0 hΛ1 hΦ
  obtain ⟨sΦ, k, hk, iΦ, fΦ⟩ := hΦ
  refine ⟨fun t ht => ?_, k, hk, fun u hu hue t => ?_, fun t ht => ?_⟩
  · unfold GlobalTheory.CosetRow.extFn at ht
    by_contra hc
    exact ht (if_neg hc)
  · have hhalf := half_add_nsmul_iff (t := t) hue k
    have hA : Φ (e₀ • (t + k • u)) = Φ (e₀ • t) := by
      rw [smul_add_nsmul]
      exact iΦ _ (hΛ0 u hu) (half_of_idem' h0 u) _
    have hB : halfInd e₁ Λ (e₁ • (t + k • u)) = halfInd e₁ Λ (e₁ • t) := by
      rw [smul_add_nsmul]
      unfold halfInd
      have hm : e₁ • t + k • (e₁ • u) ∈ Λ ↔ e₁ • t ∈ Λ :=
        Λ.add_mem_cancel_right (AddSubgroup.nsmul_mem Λ (hΛ1 u hu) k)
      have hh : IsHalf e₁ (e₁ • t + k • (e₁ • u)) ↔ IsHalf e₁ (e₁ • t) :=
        half_add_nsmul_iff (half_of_idem' h1 u) k
      by_cases hc : e₁ • t ∈ Λ ∧ IsHalf e₁ (e₁ • t)
      · rw [if_pos (And.intro (hm.2 hc.1) (hh.2 hc.2)), if_pos hc]
      · rw [if_neg (fun h => hc ⟨hm.1 h.1, hh.1 h.2⟩), if_neg hc]
    unfold GlobalTheory.CosetRow.extFn
    rw [hA, hB]
    by_cases hc : IsHalf (e₀ + e₁) t
    · rw [if_pos (hhalf.2 hc), if_pos hc]
    · rw [if_neg (mt hhalf.1 hc), if_neg hc]
  · unfold GlobalTheory.CosetRow.extFn at ht
    by_cases hc : IsHalf (e₀ + e₁) t
    · rw [if_pos hc] at ht
      have hΦt : Φ (e₀ • t) ≠ 0 := left_ne_zero_of_mul ht
      have hI : halfInd e₁ Λ (e₁ • t) ≠ 0 := right_ne_zero_of_mul ht
      have hI' : e₁ • t ∈ Λ := by
        unfold halfInd at hI
        by_contra hn
        exact hI (if_neg (fun h => hn h.1))
      have hkt : k • t = k • (e₀ • t) + k • (e₁ • t) := by
        ext i j
        have := hc i j
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul] at this ⊢
        linear_combination -(k : AE D) * this
      rw [hkt]
      exact Λ.add_mem (fΦ _ hΦt) (AddSubgroup.nsmul_mem Λ hI' k)
    · exact absurd (if_neg hc) ht

end GlobalTheory.CosetRow.ExtSB
end
