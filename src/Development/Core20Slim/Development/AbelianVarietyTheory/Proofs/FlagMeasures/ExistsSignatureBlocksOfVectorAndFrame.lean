module

public import Mathlib
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
public import Formalism.RealPlaceAnalysis.Complexify
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Subtype
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GlobalTheory.SignCount

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes    
open scoped ENNReal NNReal

private theorem qEps_eq_star_dotProduct_Jm_mulVec {m : ℕ} (ε : Fin m → Bool) (x : Fin m → ℂ) :
    ((GlobalTheory.GaussMean.qEps ε x : ℝ) : ℂ) = star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) := by
  simp only [GlobalTheory.GaussMean.qEps, Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Complex.conj_mul', Complex.star_def]
  split_ifs <;> push_cast <;> ring

private theorem qEps_mulVec_of_conjTranspose_mul_Jm_mul {m : ℕ} {ε η : Fin m → Bool} (C : Matrix (Fin m) (Fin m) ℂ)
    (h : Cᴴ * Formalism.REAL.Jm ε * C = Formalism.REAL.Jm η) (x : Fin m → ℂ) :
    GlobalTheory.GaussMean.qEps ε (C *ᵥ x) = GlobalTheory.GaussMean.qEps η x := by
  apply Complex.ofReal_injective
  rw [qEps_eq_star_dotProduct_Jm_mulVec, qEps_eq_star_dotProduct_Jm_mulVec, ← h, Matrix.star_mulVec]
  simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

private theorem qEps_not_eq_neg {m : ℕ} (ε : Fin m → Bool) (x : Fin m → ℂ) :
    GlobalTheory.GaussMean.qEps (fun a => !ε a) x = - GlobalTheory.GaussMean.qEps ε x := by
  simp only [GlobalTheory.GaussMean.qEps, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ε a = true <;> simp [h]

private theorem card_true_add_card_false_le_of_qEps_eq {m : ℕ} {ε η : Fin m → Bool} (C : Matrix (Fin m) (Fin m) ℂ)
    (hC : ∀ x, GlobalTheory.GaussMean.qEps ε (C *ᵥ x) = GlobalTheory.GaussMean.qEps η x) :
    Fintype.card {a // η a = true} + Fintype.card {a // ε a = false} ≤ m := by
  classical
  let E₁ : ({a // η a = true} → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun u a => if h : η a = true then u ⟨a, h⟩ else 0
      map_add' := by
        intro u v; funext a; by_cases h : η a = true <;> simp [h]
      map_smul' := by
        intro c u; funext a; by_cases h : η a = true <;> simp [h] }
  let E₂ : ({a // ε a = false} → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun w a => if h : ε a = false then w ⟨a, h⟩ else 0
      map_add' := by
        intro u v; funext a; by_cases h : ε a = false <;> simp [h]
      map_smul' := by
        intro c u; funext a; by_cases h : ε a = false <;> simp [h] }
  let Φ := (C.mulVecLin ∘ₗ E₁).coprod E₂
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, w⟩ hp
    have hp' : C *ᵥ E₁ u = -(E₂ w) := by
      have : C *ᵥ E₁ u + E₂ w = 0 := by simpa [Φ] using hp
      exact eq_neg_of_add_eq_zero_left this
    have hnn : ∀ a, 0 ≤ (if η a then (1 : ℝ) else -1) * ‖E₁ u a‖ ^ 2 := by
      intro a
      by_cases h : η a = true
      · simp [h]
      · simp [E₁, h]
    have hnp : GlobalTheory.GaussMean.qEps ε (-(E₂ w)) ≤ 0 := by
      unfold GlobalTheory.GaussMean.qEps
      refine Finset.sum_nonpos fun a _ => ?_
      by_cases h : ε a = false
      · simp [h]
      · simp [E₂, h]
    have hq : GlobalTheory.GaussMean.qEps η (E₁ u) = 0 := by
      refine le_antisymm ?_ (Finset.sum_nonneg fun a _ => hnn a)
      rw [← hC, hp']
      exact hnp
    have hu : u = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hnn a)).1 hq
      funext b
      have := hz b.1 (Finset.mem_univ _)
      simpa [E₁, b.2] using this
    have hw : w = 0 := by
      have h0 : E₂ w = 0 := by
        have : C *ᵥ E₁ u = 0 := by simp [hu]
        rw [hp'] at this
        exact neg_eq_zero.1 this
      funext b
      have := congrFun h0 b.1
      simpa [E₂, b.2] using this
    simp [hu, hw]
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_prod, Module.finrank_fintype_fun_eq_card] using this

theorem card_true_eq {m : ℕ} {ε η : Fin m → Bool} (C : Matrix (Fin m) (Fin m) ℂ)
    (h : Cᴴ * Formalism.REAL.Jm ε * C = Formalism.REAL.Jm η) :
    Nat.card {a // ε a = true} = Nat.card {a // η a = true} := by
  classical
  have hC := qEps_mulVec_of_conjTranspose_mul_Jm_mul C h
  have h₁ := card_true_add_card_false_le_of_qEps_eq C hC
  have hC' : ∀ x, GlobalTheory.GaussMean.qEps (fun a => !ε a) (C *ᵥ x) =
      GlobalTheory.GaussMean.qEps (fun a => !η a) x := by
    intro x; rw [qEps_not_eq_neg, qEps_not_eq_neg, hC]
  have h₂ := card_true_add_card_false_le_of_qEps_eq C hC'
  simp only [Fintype.card_subtype] at h₁ h₂
  simp only [Bool.not_eq_true', Bool.not_eq_false'] at h₂
  have hε : (Finset.univ.filter fun a => ε a = true).card +
      (Finset.univ.filter fun a => ε a = false).card = m := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    have : ∀ a : Fin m, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
      intro a; cases ε a <;> simp
    simp [this]
  have hη : (Finset.univ.filter fun a => η a = true).card +
      (Finset.univ.filter fun a => η a = false).card = m := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    have : ∀ a : Fin m, ((if η a = true then 1 else 0) + (if η a = false then 1 else 0) : ℕ) = 1 := by
      intro a; cases η a <;> simp
    simp [this]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]
  omega





end GlobalTheory.SignCount
