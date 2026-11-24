module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarDecompositionIndefiniteUnitaryStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryCharacterMaximalCompactDetPowStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryCharacterEqOneCayleyRotationStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfCayleyTwoIZpowEqOneForallStatement
public import Batteries.Logic
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section
namespace GlobalTheory.RealLift.CharTrace
open scoped Matrix
open GlobalTheory.RealLift.OneParam

variable {R S : ℕ}

theorem jm_eq : Jm R S = Matrix.fromBlocks 1 0 0 (-1) := rfl

theorem jm_conjTranspose : (Jm R S)ᴴ = Jm R S := by
  rw [jm_eq, Matrix.fromBlocks_conjTranspose]; simp

theorem ne_zero_add (x : ℝ) : (1 + 2 * Complex.I * x : ℂ) ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp at this

theorem ne_zero_sub (x : ℝ) : (1 - 2 * Complex.I * x : ℂ) ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp at this

theorem star_zeta (x : ℝ) : star ((1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x)) =
    (1 - 2 * Complex.I * x) / (1 + 2 * Complex.I * x) := by
  rw [star_div₀]; congr 1 <;> simp [Complex.ext_iff]

theorem diag_unit {m : Type} [Fintype m] [DecidableEq m] (i0 : m) (z : ℂ) (hz : star z * z = 1) :
    (Matrix.diagonal (Function.update (1 : m → ℂ) i0 z))ᴴ * Matrix.diagonal (Function.update 1 i0 z) = 1 := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i
  by_cases hi : i = i0
  · subst hi; simpa using hz
  · simp [Function.update_of_ne hi]

theorem det_diag {m : Type} [Fintype m] [DecidableEq m] (i0 : m) (z : ℂ) :
    (Matrix.diagonal (Function.update (1 : m → ℂ) i0 z)).det = z := by
  rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]; simp

theorem charUpq : ∀ (R S : ℕ) (χ : Mat R S → ℂ),
    (∀ g h : Mat R S, gᴴ * Jm R S * g = Jm R S → hᴴ * Jm R S * h = Jm R S → χ (g * h) = χ g * χ h) →
    ContinuousOn χ {g : Mat R S | gᴴ * Jm R S * g = Jm R S} →
    (∀ g : Mat R S, gᴴ * Jm R S * g = Jm R S → χ g ≠ 0) →
    ∃ n : ℤ, ∀ g : Mat R S, gᴴ * Jm R S * g = Jm R S → χ g = g.det ^ n := by
  intro R S χ hmul hc hne
  obtain ⟨x, y, hxy⟩ := GlobalTheory.T.indefiniteUnitaryCharacter_maximalCompact_det_pow R S χ hmul hc hne
  have hJJ : Jm R S * Jm R S = 1 := jm_mul_self
  have h1 : χ 1 = 1 := by
    have e := hmul 1 1 (by simp) (by simp)
    rw [mul_one] at e
    exact mul_left_cancel₀ (hne 1 (by simp)) (e.symm.trans (mul_one _).symm)
  have hJU : (Jm R S)ᴴ * Jm R S * Jm R S = Jm R S := by rw [jm_conjTranspose, hJJ, Matrix.one_mul]
  have hχJ : χ (Jm R S) * χ (Jm R S) = 1 := by rw [← hmul _ _ hJU hJU, hJJ, h1]
  have memm : ∀ {g h : Mat R S}, gᴴ * Jm R S * g = Jm R S → hᴴ * Jm R S * h = Jm R S →
      (g * h)ᴴ * Jm R S * (g * h) = Jm R S := fun {g h} hg hh => by
    calc (g * h)ᴴ * Jm R S * (g * h) = hᴴ * (gᴴ * Jm R S * g) * h := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Jm R S := by rw [hg, hh]
  have blk : ∀ k : Mat R S, kᴴ * Jm R S * k = Jm R S → Jm R S * k = k * Jm R S →
      ∃ (a : Matrix (Fin R) (Fin R) ℂ) (d : Matrix (Fin S) (Fin S) ℂ), aᴴ * a = 1 ∧ dᴴ * d = 1 ∧
        k = Matrix.fromBlocks a 0 0 d := by
    intro k hkG hkJ
    obtain ⟨a, b, b', d, hmm⟩ : ∃ a b b' d, k = Matrix.fromBlocks a b b' d :=
      ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks k).symm⟩
    subst hmm
    rw [jm_eq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hkJ
    obtain ⟨-, e1, e2, -⟩ := hkJ
    simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_one, add_zero, zero_add] at e1 e2
    have hb : b = 0 := by
      ext i j
      have : b i j = - b i j := congrFun (congrFun e1 i) j
      show b i j = 0
      linear_combination this / 2
    have hb' : b' = 0 := by
      ext i j
      have : - b' i j = b' i j := congrFun (congrFun e2 i) j
      show b' i j = 0
      linear_combination -this / 2
    subst hb hb'
    rw [jm_eq] at hkG
    have := hkG
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply] at this
    exact ⟨a, d, this.1, this.2, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, ∀ (a : Matrix (Fin R) (Fin R) ℂ) (d : Matrix (Fin S) (Fin S) ℂ),
      a.det ^ x * d.det ^ y = (a.det * d.det) ^ n := by
    rcases Nat.eq_zero_or_pos R with hR | hR
    · subst hR; exact ⟨y, fun a d => by simp [Matrix.det_isEmpty]⟩
    rcases Nat.eq_zero_or_pos S with hS | hS
    · subst hS; exact ⟨x, fun a d => by simp [Matrix.det_isEmpty]⟩
    have hxy' : x = y := by
      have h0 := GlobalTheory.T.eq_zero_of_cayley_two_I_zpow_eq_one_forall (x - y) (fun t => by
        have e := GlobalTheory.T.indefiniteUnitaryCharacter_eq_one_cayleyRotation R S χ hmul hc hne ⟨0, hR⟩ ⟨0, hS⟩ t
        have hu1 := diag_unit (⟨0, hR⟩ : Fin R) ((1 + 2 * Complex.I * t) / (1 - 2 * Complex.I * t)) (by
          rw [star_zeta]; field_simp [ne_zero_add t, ne_zero_sub t])
        have hu2 := diag_unit (⟨0, hS⟩ : Fin S) ((1 - 2 * Complex.I * t) / (1 + 2 * Complex.I * t)) (by
          rw [star_div₀]
          have e1 : star (1 - 2 * Complex.I * t) = 1 + 2 * Complex.I * t := by simp [Complex.ext_iff]
          have e2 : star (1 + 2 * Complex.I * t) = 1 - 2 * Complex.I * t := by simp [Complex.ext_iff]
          rw [e1, e2]; field_simp [ne_zero_add t, ne_zero_sub t])
        rw [hxy _ _ hu1 hu2, det_diag, det_diag] at e
        have hz : ((1 + 2 * Complex.I * t) / (1 - 2 * Complex.I * t)) ≠ 0 :=
          div_ne_zero (ne_zero_add t) (ne_zero_sub t)
        have einv : (1 - 2 * Complex.I * t) / (1 + 2 * Complex.I * t) = ((1 + 2 * Complex.I * t) / (1 - 2 * Complex.I * t))⁻¹ := by
          rw [inv_div]
        rw [einv, inv_zpow', ← zpow_add₀ hz] at e
        rw [sub_eq_add_neg]; exact e)
      omega
    subst hxy'
    exact ⟨x, fun a d => (mul_zpow _ _ _).symm⟩
  refine ⟨n, fun g hg => ?_⟩
  obtain ⟨k, q, hk1, hk2, hq1, hq2, rfl⟩ := GlobalTheory.T.exists_polar_decomposition_indefiniteUnitary R S g hg
  have hq : χ q * χ q = 1 := by
    have hJq : (Jm R S * q)ᴴ * Jm R S * (Jm R S * q) = Jm R S := memm hJU hq1
    have hJqJ := memm hJq hJU
    have e : χ (Jm R S * q * Jm R S * q) = χ (Jm R S) * χ q * χ (Jm R S) * χ q := by
      rw [hmul _ _ hJqJ hq1, hmul _ _ hJq hJU, hmul _ _ hJU hq1]
    rw [hq2, h1] at e
    calc χ q * χ q = (χ (Jm R S) * χ (Jm R S)) * (χ q * χ q) := by rw [hχJ, one_mul]
      _ = 1 := by rw [e]; ring
  have hdq : q.det * q.det = 1 := by
    have e := congrArg Matrix.det hq2
    have eJ := congrArg Matrix.det hJJ
    simp only [Matrix.det_mul, Matrix.det_one] at e eJ
    calc q.det * q.det = (Jm R S).det * (Jm R S).det * (q.det * q.det) := by rw [eJ, one_mul]
      _ = 1 := by rw [← e]; ring
  obtain ⟨a, d, ha, hd, rfl⟩ := blk k hk1 hk2
  rw [hmul _ _ (memm hk1 hq1) hq1, hmul _ _ hk1 hq1, mul_assoc, hq, mul_one, hxy a d ha hd, hn a d,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, mul_assoc, hdq, mul_one]

theorem jm_map_star : (Jm R S).map star = Jm R S := by
  ext a b; rcases a with i | i <;> rcases b with j | j <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks, Matrix.one_apply] <;> split_ifs <;> simp

theorem form_iff (h : Mat R S) : hᴴ * Jm R S * h = Jm R S ↔ hᵀ * Jm R S * h.map star = Jm R S := by
  have e1 : (hᴴ).map star = hᵀ := by ext i j; simp [Matrix.conjTranspose_apply]
  have e2 : (hᵀ).map star = hᴴ := by ext i j; simp [Matrix.conjTranspose_apply]
  have e3 : (h.map star).map star = h := by ext i j; simp
  constructor
  · intro hh
    have := congrArg (fun X => X.map star) hh
    simp only [map_star_mul, jm_map_star, e1] at this
    exact this
  · intro hh
    have := congrArg (fun X => X.map star) hh
    simp only [map_star_mul, jm_map_star, e2, e3] at this
    exact this

theorem mem_mul {g h : Mat R S} (hg : gᴴ * Jm R S * g = Jm R S) (hh : hᴴ * Jm R S * h = Jm R S) :
    (g * h)ᴴ * Jm R S * (g * h) = Jm R S := by
  calc (g * h)ᴴ * Jm R S * (g * h) = hᴴ * (gᴴ * Jm R S * g) * h := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm R S := by rw [hg, hh]

theorem mem_one : (1 : Mat R S)ᴴ * Jm R S * 1 = Jm R S := by simp

theorem prod_char {ι : Type} [Fintype ι] [DecidableEq ι] (χ : (ι → Mat R S) → ℂ)
    (hmul : ∀ g h : ι → Mat R S, (∀ w, (g w)ᴴ * Jm R S * g w = Jm R S) → (∀ w, (h w)ᴴ * Jm R S * h w = Jm R S) →
      χ (g * h) = χ g * χ h)
    (hc : ContinuousOn χ {g | ∀ w, (g w)ᴴ * Jm R S * g w = Jm R S})
    (hne : ∀ g : ι → Mat R S, (∀ w, (g w)ᴴ * Jm R S * g w = Jm R S) → χ g ≠ 0) :
    ∃ n : ι → ℤ, ∀ g : ι → Mat R S, (∀ w, (g w)ᴴ * Jm R S * g w = Jm R S) → χ g = ∏ w, (g w).det ^ n w := by
  have upd : ∀ w (a : Mat R S), aᴴ * Jm R S * a = Jm R S → ∀ v,
      (Function.update (1 : ι → Mat R S) w a v)ᴴ * Jm R S * Function.update (1 : ι → Mat R S) w a v = Jm R S := by
    intro w a ha v
    by_cases hv : v = w
    · subst hv; simpa using ha
    · rw [Function.update_of_ne hv]; exact mem_one
  have key : ∀ w, ∃ n : ℤ, ∀ a : Mat R S, aᴴ * Jm R S * a = Jm R S →
      χ (Function.update (1 : ι → Mat R S) w a) = a.det ^ n := by
    intro w
    refine charUpq R S (fun a => χ (Function.update (1 : ι → Mat R S) w a)) ?_ ?_ ?_
    · intro a b ha hb
      have e : Function.update (1 : ι → Mat R S) w (a * b) =
          Function.update (1 : ι → Mat R S) w a * Function.update (1 : ι → Mat R S) w b := by
        funext v
        by_cases hv : v = w
        · subst hv; simp
        · simp [Function.update_of_ne hv]
      rw [e]
      exact hmul _ _ (upd w a ha) (upd w b hb)
    · exact hc.comp (show Continuous (Function.update (1 : ι → Mat R S) w) from continuous_const.update w continuous_id).continuousOn
        fun a ha => upd w a ha
    · intro a ha; exact hne _ (upd w a ha)
  choose n hn using key
  refine ⟨n, fun g hg => ?_⟩
  have h1 : χ 1 = 1 := by
    have e := hmul 1 1 (fun _ => mem_one) (fun _ => mem_one)
    rw [mul_one] at e
    have hz := hne 1 (fun _ => mem_one)
    exact mul_left_cancel₀ hz (e.symm.trans (mul_one _).symm)
  have pc : ∀ (s : Finset ι) v, (s.piecewise g 1 v)ᴴ * Jm R S * s.piecewise g 1 v = Jm R S := by
    intro s v
    by_cases hv : v ∈ s
    · rw [Finset.piecewise_eq_of_mem _ _ _ hv]; exact hg v
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hv]; exact mem_one
  have ind : ∀ s : Finset ι, χ (s.piecewise g 1) = ∏ w ∈ s, (g w).det ^ n w := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h1
    | insert a s ha ih =>
      have e : (insert a s).piecewise g 1 = Function.update (1 : ι → Mat R S) a (g a) * s.piecewise g 1 := by
        funext v
        by_cases hv : v = a
        · subst hv; simp [Finset.piecewise, ha]
        · simp [Finset.piecewise, hv, Function.update_of_ne hv]
      rw [e, hmul _ _ (upd a (g a) (hg a)) (pc s), hn a (g a) (hg a), ih, Finset.prod_insert ha]
  simpa using ind Finset.univ

theorem conj_unit {β : Type} [Fintype β] [DecidableEq β] {N : Matrix β β ℂ} {C : Matrix β (Ix R S) ℂ}
    {C' : Matrix (Ix R S) β ℂ} (hF : Cᵀ * N * C.map star = Jm R S) (hR : C * C' = 1) {h : Mat R S}
    (hh : hᵀ * Jm R S * h.map star = Jm R S) :
    (C * h * C')ᵀ * N * (C * h * C').map star = N := by
  calc (C * h * C')ᵀ * N * (C * h * C').map star
        = C'ᵀ * (hᵀ * (Cᵀ * N * C.map star) * h.map star) * C'.map star := by
          rw [map_star_mul, map_star_mul, Matrix.transpose_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = C'ᵀ * (Cᵀ * N * C.map star) * C'.map star := by rw [hF, hh, ← hF]
      _ = (C * C')ᵀ * N * (C * C').map star := by
          rw [map_star_mul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = N := by
          rw [hR, Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (by simp) (by simp), Matrix.mul_one]


end GlobalTheory.RealLift.CharTrace
