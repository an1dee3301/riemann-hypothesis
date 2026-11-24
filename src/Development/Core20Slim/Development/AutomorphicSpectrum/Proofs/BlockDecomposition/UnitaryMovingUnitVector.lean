module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramMatrixLocalGlobal
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.ByCases
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypUnit

section Form

variable {K : Type} [CommRing K] {M : ℕ}

theorem fin_three {P : Fin (M + 2) → Prop} (h0 : P 0) (h1 : P 1) (h2 : ∀ i : Fin M, P i.succ.succ)
    (i : Fin (M + 2)) : P i :=
  Fin.cases h0 (fun i => Fin.cases h1 (fun i => h2 i) i) i

theorem sum_three (f : Fin (M + 2) → K) : ∑ i, f i = f 0 + f 1 + ∑ i : Fin M, f i.succ.succ := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  exact (add_assoc _ _ _).symm

variable (s : K →+* K) (A : Matrix (Fin M) (Fin M) K)

theorem hform_hypOne (x y : Fin (M + 2) → K) :
    hform s (hypOne A) x y = s (x 0) * y 1 + s (x 1) * y 0 + hform s A (tailH x) (tailH y) := by
  simp only [hform, sum_three, hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one,
    hypOne_zero_rest, hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, tailH]
  simp

theorem hform_add_right (x y y' : Fin M → K) :
    hform s A x (y + y') = hform s A x y + hform s A x y' := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_add_left (x x' y : Fin M → K) :
    hform s A (x + x') y = hform s A x y + hform s A x' y := by
  simp only [hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_smul_right (c : K) (x y : Fin M → K) :
    hform s A x (c • y) = c * hform s A x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_smul_left (c : K) (x y : Fin M → K) :
    hform s A (c • x) y = s c * hform s A x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_conj (hs : ∀ e, s (s e) = e) (hA : ∀ i j, s (A j i) = A i j) (x y : Fin M → K) :
    s (hform s A x y) = hform s A y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform, map_sum, map_mul, hs]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hA]; ring

def cvK (c : K) (x v : Fin (M + 2) → K) : Fin (M + 2) → K :=
  vH (x 0 * v 0)
    (v 0 * x 1 + Ring.inverse (s (x 0)) * (v 1 - c * v 0 - hform s A (tailH x) (tailH v)))
    (fun i => v 0 * x i.succ.succ + v i.succ.succ)

def cvL (c : K) (x : Fin (M + 2) → K) : (Fin (M + 2) → K) →ₗ[K] (Fin (M + 2) → K) where
  toFun := cvK s A c x
  map_add' u v := by
    have ht : tailH (u + v) = tailH u + tailH v := rfl
    funext i
    refine fin_three (P := fun i => cvK s A c x (u + v) i = (cvK s A c x u + cvK s A c x v) i) ?_ ?_ ?_ i
    · show x 0 * (u 0 + v 0) = x 0 * u 0 + x 0 * v 0
      ring
    · show (u 0 + v 0) * x 1 + Ring.inverse (s (x 0)) *
          (u 1 + v 1 - c * (u 0 + v 0) - hform s A (tailH x) (tailH (u + v))) =
        (u 0 * x 1 + Ring.inverse (s (x 0)) * (u 1 - c * u 0 - hform s A (tailH x) (tailH u))) +
        (v 0 * x 1 + Ring.inverse (s (x 0)) * (v 1 - c * v 0 - hform s A (tailH x) (tailH v)))
      rw [ht, hform_add_right]
      ring
    · intro i
      show (u 0 + v 0) * x i.succ.succ + (u i.succ.succ + v i.succ.succ) =
        (u 0 * x i.succ.succ + u i.succ.succ) + (v 0 * x i.succ.succ + v i.succ.succ)
      ring
  map_smul' e v := by
    have ht : tailH (e • v) = e • tailH v := rfl
    funext i
    refine fin_three (P := fun i => cvK s A c x (e • v) i = (e • cvK s A c x v) i) ?_ ?_ ?_ i
    · show x 0 * (e * v 0) = e * (x 0 * v 0)
      ring
    · show (e * v 0) * x 1 + Ring.inverse (s (x 0)) *
          (e * v 1 - c * (e * v 0) - hform s A (tailH x) (tailH (e • v))) =
        e * (v 0 * x 1 + Ring.inverse (s (x 0)) * (v 1 - c * v 0 - hform s A (tailH x) (tailH v)))
      rw [ht, hform_smul_right]
      ring
    · intro i
      show (e * v 0) * x i.succ.succ + e * v i.succ.succ = e * (v 0 * x i.succ.succ + v i.succ.succ)
      ring

theorem hform_cvK (hs : ∀ e, s (s e) = e) (hA : ∀ i j, s (A j i) = A i j) (c : K)
    (x : Fin (M + 2) → K) (hx : IsUnit (x 0)) (hc : c + s c = hform s (hypOne A) x x)
    (u v : Fin (M + 2) → K) :
    hform s (hypOne A) (cvK s A c x u) (cvK s A c x v) = hform s (hypOne A) u v := by
  have hsa : IsUnit (s (x 0)) := hx.map s
  have hab : s (x 0) * Ring.inverse (s (x 0)) = 1 := Ring.mul_inverse_cancel _ hsa
  have hba : s (Ring.inverse (s (x 0))) * x 0 = 1 := by
    have := congrArg s hab
    rwa [map_mul, hs, map_one, mul_comm] at this
  have htail : ∀ w : Fin (M + 2) → K, tailH (cvK s A c x w) = w 0 • tailH x + tailH w := fun _ => rfl
  rw [hform_hypOne, hform_hypOne s A u v, htail, htail, hform_add_left, hform_add_right,
    hform_add_right, hform_smul_left, hform_smul_left, hform_smul_right, hform_smul_right]
  rw [hform_hypOne] at hc
  have hconj := hform_conj s A hs hA (tailH x) (tailH u)
  have e0 : ∀ w : Fin (M + 2) → K, cvK s A c x w 0 = x 0 * w 0 := fun _ => rfl
  have e1 : ∀ w : Fin (M + 2) → K, cvK s A c x w 1 = w 0 * x 1 + Ring.inverse (s (x 0)) *
      (w 1 - c * w 0 - hform s A (tailH x) (tailH w)) := fun _ => rfl
  rw [e0, e0, e1, e1]
  simp only [map_add (f := _), map_sub, map_mul, hconj]
  linear_combination (s (u 0) * (v 1 - c * v 0 - hform s A (tailH x) (tailH v))) * hab +
    (v 0 * (s (u 1) - s c * s (u 0) - hform s A (tailH u) (tailH x))) * hba -
    (s (u 0) * v 0) * hc

theorem cvK_surjective (c : K) (x : Fin (M + 2) → K) (hx : IsUnit (x 0)) (hs : IsUnit (s (x 0))) :
    Function.Surjective (cvK s A c x) := by
  intro w
  have ha : x 0 * Ring.inverse (x 0) = 1 := Ring.mul_inverse_cancel _ hx
  have hb : Ring.inverse (s (x 0)) * s (x 0) = 1 := Ring.inverse_mul_cancel _ hs
  set α := Ring.inverse (x 0) * w 0 with hα
  set U : Fin M → K := fun i => w i.succ.succ - α * x i.succ.succ with hU
  refine ⟨vH α (s (x 0) * (w 1 - α * x 1) + c * α + hform s A (tailH x) U) U, ?_⟩
  funext i
  refine fin_three (P := fun i => cvK s A c x
    (vH α (s (x 0) * (w 1 - α * x 1) + c * α + hform s A (tailH x) U) U) i = w i) ?_ ?_ ?_ i
  · show x 0 * α = w 0
    rw [hα, ← mul_assoc, ha, one_mul]
  · show α * x 1 + Ring.inverse (s (x 0)) *
      (s (x 0) * (w 1 - α * x 1) + c * α + hform s A (tailH x) U - c * α - hform s A (tailH x) U) = w 1
    linear_combination (w 1 - α * x 1) * hb
  · intro i
    show α * x i.succ.succ + U i = w i.succ.succ
    rw [hU]
    ring

theorem cT_mul_apply (H C : Matrix (Fin M) (Fin M) K) (i j : Fin M) :
    (Formalism.UG.cT s C * H * C) i j = hform s H (fun k => C k i) (fun k => C k j) := by
  simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hform,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem hform_single (H : Matrix (Fin M) (Fin M) K) (i j : Fin M) :
    hform s H (Pi.single i 1) (Pi.single j 1) = H i j := by
  simp [hform, Pi.single_apply, apply_ite s]

theorem exists_unitary (hs : ∀ e, s (s e) = e) (hA : ∀ i j, s (A j i) = A i j) (c : K)
    (x : Fin (M + 2) → K) (hx : IsUnit (x 0)) (hc : c + s c = hform s (hypOne A) x x) :
    ∃ g : GL (Fin (M + 2)) K, g ∈ Formalism.UG.UJ s (hypOne A) ∧
      ∀ v, (g : Matrix (Fin (M + 2)) (Fin (M + 2)) K).mulVec v = cvK s A c x v := by
  set C := LinearMap.toMatrix' (cvL s A c x) with hC
  have hmul : ∀ v, C.mulVec v = cvK s A c x v := fun v => by
    rw [hC, LinearMap.toMatrix'_mulVec]
    rfl
  have hunit : IsUnit C := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro w
    obtain ⟨v, hv⟩ := cvK_surjective s A c x hx (hx.map s) w
    exact ⟨v, (hmul v).trans hv⟩
  obtain ⟨g, hg⟩ := hunit
  refine ⟨g, ?_, fun v => by rw [hg, hmul]⟩
  show Formalism.UG.cT s (g : Matrix (Fin (M + 2)) (Fin (M + 2)) K) * hypOne A * g = hypOne A
  rw [hg]
  ext i j
  rw [cT_mul_apply]
  have hcol : ∀ k, (fun l => C l k) = cvK s A c x (Pi.single k 1) := fun k => by
    rw [← hmul, Matrix.mulVec_single_one]
    rfl
  rw [hcol, hcol, hform_cvK s A hs hA c x hx hc, hform_single]

end Form

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_inclR_apply (σ : E →ₐ[F] E) (e : E) :
    sigR R σ (inclR (F := F) R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem JR_hypOne {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    JR R (hypOne J) = hypOne (JR (F := F) R J) := by
  ext i j
  refine fin_three (P := fun i => JR (F := F) R (hypOne J) i j = hypOne (JR (F := F) R J) i j) ?_ ?_ ?_ i
  · refine fin_three (P := fun j => JR (F := F) R (hypOne J) 0 j = hypOne (JR (F := F) R J) 0 j) ?_ ?_ ?_ j
    · simp [JR, hypOne_zero_zero]
    · simp [JR, hypOne_zero_one]
    · intro j; simp [JR, hypOne_zero_rest]
  · refine fin_three (P := fun j => JR (F := F) R (hypOne J) 1 j = hypOne (JR (F := F) R J) 1 j) ?_ ?_ ?_ j
    · simp [JR, hypOne_one_zero]
    · simp [JR, hypOne_one_one]
    · intro j; simp [JR, hypOne_one_rest]
  · intro i
    refine fin_three (P := fun j => JR (F := F) R (hypOne J) i.succ.succ j =
      hypOne (JR (F := F) R J) i.succ.succ j) ?_ ?_ ?_ j
    · simp [JR, hypOne_rest_zero]
    · simp [JR, hypOne_rest_one]
    · intro j; simp [JR, hypOne_rest_rest]

end Tensor

theorem cvec_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (x : Fin (M + 2) → R ⊗[F] E), IsUnit (x 0) → ∃ g : HA R σ (hypOne J), ∀ v : Fin (M + 2) → R ⊗[F] E, ((HA.mat R σ (hypOne J) g : GL (Fin (M + 2)) (R ⊗[F] E)) : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)).mulVec v = cvec R σ J x v := by
  intro F E _ _ _ _ _ σ hcm M J hJ R _ _ x hx
  have hinv := sig_invol σ hcm
  have hs : ∀ e, sigR R σ (sigR R σ e) = e := sigR_sigR R σ hinv
  have hA : ∀ i j, sigR R σ (JR (F := F) R J j i) = JR (F := F) R J i j := fun i j => by
    show sigR R σ (inclR R (J j i)) = inclR R (J i j)
    rw [sigR_inclR_apply, hJ.1]
  have ht : hR R σ (hypOne J) x x = hform (sigR R σ) (hypOne (JR (F := F) R J)) x x := by
    rw [hR, JR_hypOne]
  have htc : sigR R σ (hR R σ (hypOne J) x x) = hR R σ (hypOne J) x x := by
    rw [ht, hform_hypOne]
    simp only [map_add (f := _), map_mul, hs, hform_conj (sigR R σ) (JR (F := F) R J) hs hA]
    ring
  have hhalf : sigR R σ (halfR (F := F) (E := E) R) = halfR (F := F) (E := E) R := by
    rw [halfR, sigR_inclR_apply, AlgHom.commutes]
  have h2 : halfR (F := F) (E := E) R + halfR (F := F) (E := E) R = 1 := by
    rw [halfR, ← map_add (f := _), ← map_add (f := _)]
    norm_num
  have hc : tHalf R σ J x + sigR R σ (tHalf R σ J x) =
      hform (sigR R σ) (hypOne (JR (F := F) R J)) x x := by
    rw [tHalf, map_mul, hhalf, htc, ← ht]
    linear_combination (hR R σ (hypOne J) x x) * h2
  obtain ⟨g, hg, hv⟩ := exists_unitary (sigR R σ) (JR (F := F) R J) hs hA (tHalf R σ J x) x hx hc
  refine ⟨⟨g, ?_⟩, hv⟩
  show g ∈ Formalism.UG.UJ (sigR R σ) (JR R (hypOne J))
  rw [JR_hypOne]
  exact hg

end GlobalTheory.CompanionTheory.WeilSiegel.HypUnit
