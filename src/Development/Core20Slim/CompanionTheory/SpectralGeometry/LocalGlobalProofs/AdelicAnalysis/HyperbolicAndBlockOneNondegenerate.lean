module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BlockForm

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem blockOne_zero_zero {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    blockOne t A 0 0 = t := rfl

theorem blockOne_zero_succ {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K)
    (j : Fin M) : blockOne t A 0 j.succ = 0 := rfl

theorem blockOne_succ_zero {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K)
    (i : Fin M) : blockOne t A i.succ 0 = 0 := rfl

theorem blockOne_succ_succ {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K)
    (i j : Fin M) : blockOne t A i.succ j.succ = A i j := rfl

theorem det_blockOne {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  have h0 : (blockOne t A).submatrix Fin.succ Fin.succ = A := by
    ext i j
    exact blockOne_succ_succ t A i j
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [blockOne_zero_zero, blockOne_zero_succ, h0]

theorem hypJ_zero_zero {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    hypJ A 0 0 = 0 := rfl

theorem hypJ_zero_one {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    hypJ A 0 1 = 1 := by
  rw [← Fin.succ_zero_eq_one]; rfl

theorem hypJ_zero_succ_succ {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (j : Fin M) : hypJ A 0 j.succ.succ = 0 := rfl

theorem hypJ_one_zero {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    hypJ A 1 0 = 1 := by
  rw [← Fin.succ_zero_eq_one]; rfl

theorem hypJ_one_one {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    hypJ A 1 1 = 0 := by
  rw [← Fin.succ_zero_eq_one]; rfl

theorem hypJ_one_succ_succ {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (j : Fin M) : hypJ A 1 j.succ.succ = 0 := by
  rw [← Fin.succ_zero_eq_one]; rfl

theorem hypJ_succ_succ_zero {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (i : Fin M) : hypJ A i.succ.succ 0 = 0 := rfl

theorem hypJ_succ_succ_one {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (i : Fin M) : hypJ A i.succ.succ 1 = 0 := by
  rw [← Fin.succ_zero_eq_one]; rfl

theorem hypJ_succ_succ_succ_succ {K : Type} [Zero K] [One K] {M : ℕ}
    (A : Matrix (Fin M) (Fin M) K) (i j : Fin M) : hypJ A i.succ.succ j.succ.succ = A i j := rfl

theorem det_hypJ {K : Type} [CommRing K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    (hypJ A).det = -A.det := by
  have h1 : (hypJ A).submatrix Fin.succ (Fin.succAbove 1) = blockOne 1 A := by
    rw [← Fin.succ_zero_eq_one]
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · rfl
    · rfl
    · rfl
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [hypJ_zero_zero, hypJ_zero_one, hypJ_zero_succ_succ, h1, det_blockOne]

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem isHermND_hypJ (σ : E →ₐ[F] E) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) : IsHermND σ (hypJ J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [hypJ_zero_zero]
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [hypJ_zero_one, hypJ_one_zero]
        · simp [hypJ_zero_succ_succ, hypJ_succ_succ_zero]
    · refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [hypJ_zero_one, hypJ_one_zero]
        · refine Fin.cases ?_ (fun j => ?_) j
          · simp [hypJ_one_one]
          · simp [hypJ_one_succ_succ, hypJ_succ_succ_one]
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [hypJ_zero_succ_succ, hypJ_succ_succ_zero]
        · refine Fin.cases ?_ (fun j => ?_) j
          · simp [hypJ_one_succ_succ, hypJ_succ_succ_one]
          · rw [hypJ_succ_succ_succ_succ, hypJ_succ_succ_succ_succ]
            exact hJ.1 i j
  · rw [det_hypJ]
    exact neg_ne_zero.mpr hJ.2

theorem isHermND_blockOne (σ : E →ₐ[F] E) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) {t : F} (ht : t ≠ 0) : IsHermND σ (blockOne (algebraMap F E t) J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [blockOne_zero_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · rw [blockOne_succ_succ, blockOne_succ_succ]
      exact hJ.1 i j
  · rw [det_blockOne]
    exact mul_ne_zero ((map_ne_zero (algebraMap F E)).mpr ht) hJ.2

theorem blockForms_isHermND : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHermND σ (hypJ J) ∧
      ∀ t : F, t ≠ 0 → IsHermND σ (blockOne (algebraMap F E t) J) :=
  fun _ _ _ _ _ _ _ σ _ _ _ hJ => ⟨isHermND_hypJ σ hJ, fun _ ht => isHermND_blockOne σ hJ ht⟩

end GlobalTheory.CompanionTheory.SW.BlockForm
