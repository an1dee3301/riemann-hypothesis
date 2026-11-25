module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHermAtPlace
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PGramAtData
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementForm
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem real_smul_vec (c : ℝ) (z : ι → ℂ) : c • z = (c : ℂ) • z := by
  ext i
  simp [Complex.real_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem map_conj_transpose (M : Matrix ι ι ℂ) : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := rfl

theorem hyperbolic_at_place (h : HermitianForm F E W) (v : Basis ι E W) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (w : InfinitePlace E) :
    (gramAt h v w).IsHermitian ∧ IsUnit (gramAt h v w).det ∧
      hForm (gramAt h v w) (vecAt v x₀ w) (vecAt v x₀ w) = 0 ∧
      hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v w₀ w) = 0 ∧
      hForm (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) = 1 := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨(GramAtData.proof h v w).1, (GramAtData.proof h v w).2, ?_, ?_, ?_⟩
  · rw [hForm, ← HermAtPlace.proof h v w, h1, map_zero]
  · rw [hForm, ← HermAtPlace.proof h v w, h2, map_zero]
  · rw [hForm, ← HermAtPlace.proof h v w, h3, map_one]


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem archUnitary_at_place {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v)
    (w : InfinitePlace E) :
    (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ))ᴴ * gramAt h v w *
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = gramAt h v w := by
  rw [← map_conj_transpose]
  exact mem_archUnitary.1 g.2 w

def heisY (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    Submodule ℝ (InfinitePlace E → ι → ℂ) where
  carrier := {y | ∀ w, hForm (gramAt h v w) (vecAt v x₀ w) (y w) = 0 ∧
    hForm (gramAt h v w) (vecAt v w₀ w) (y w) = 0}
  add_mem' {y z} hy hz w := by
    simp only [Pi.add_apply, hForm_add_right, (hy w).1, (hz w).1, (hy w).2, (hz w).2, add_zero,
      and_self]
  zero_mem' w := ⟨hForm_zero_right _ _, hForm_zero_right _ _⟩
  smul_mem' c y hy w := by
    simp only [Pi.smul_apply, real_smul_vec, hForm_smul_right, (hy w).1, (hy w).2, mul_zero,
      and_self]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [DecidableEq ι] in
theorem mem_heisY {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}
    {y : InfinitePlace E → ι → ℂ} : y ∈ heisY h v x₀ w₀ ↔
      ∀ w, hForm (gramAt h v w) (vecAt v x₀ w) (y w) = 0 ∧
        hForm (gramAt h v w) (vecAt v w₀ w) (y w) = 0 := Iff.rfl

abbrev HeisCoord (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :=
  heisY h v x₀ w₀ × (InfinitePlace E → ℝ)

def heisMatAt (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W)
    (y : InfinitePlace E → ι → ℂ) (t : InfinitePlace E → ℝ) (w : InfinitePlace E) :
    Matrix ι ι ℂ :=
  heisMat (gramAt h v w) (vecAt v x₀ w) (y w) (heisS (gramAt h v w) (y w) (t w))

omit [DecidableEq ι] in
theorem heisS_add {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (y₁ y₂ : ι → ℂ) (t₁ t₂ : ℝ) :
    heisS H y₁ t₁ + heisS H y₂ t₂ - hForm H y₁ y₂ =
      heisS H (y₁ + y₂) (t₁ + t₂ - (hForm H y₁ y₂).im) := by
  have hs : (heisS H y₁ t₁ + heisS H y₂ t₂ - hForm H y₁ y₂) +
      starRingEnd ℂ (heisS H y₁ t₁ + heisS H y₂ t₂ - hForm H y₁ y₂) +
      hForm H (y₁ + y₂) (y₁ + y₂) = 0 := by
    have e1 := heisS_spec hH y₁ t₁
    have e2 := heisS_spec hH y₂ t₂
    have e3 := hForm_conj hH y₁ y₂
    simp only [map_add (f := _), map_sub, hForm_add_left, hForm_add_right]
    linear_combination e1 + e2 - e3
  rw [eq_heisS hs]
  congr 1

section Coords

variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

theorem heisMatAt_mul (hp : IsHyperbolicPair h x₀ w₀) {y₁ y₂ : InfinitePlace E → ι → ℂ}
    (hy₁ : y₁ ∈ heisY h v x₀ w₀) (hy₂ : y₂ ∈ heisY h v x₀ w₀) (t₁ t₂ : InfinitePlace E → ℝ)
    (w : InfinitePlace E) :
    heisMatAt h v x₀ y₁ t₁ w * heisMatAt h v x₀ y₂ t₂ w = heisMatAt h v x₀ (y₁ + y₂)
      (t₁ + t₂ - fun w => (hForm (gramAt h v w) (y₁ w) (y₂ w)).im) w := by
  obtain ⟨hH, -, ha, -, -⟩ := hyperbolic_at_place h v hp w
  rw [heisMatAt, heisMatAt, heisMat_mul hH ha (hy₁ w).1 (hy₂ w).1, heisS_add hH, heisMatAt]
  rfl

def heisUnit (hp : IsHyperbolicPair h x₀ w₀) (y : heisY h v x₀ w₀) (t : InfinitePlace E → ℝ)
    (w : InfinitePlace E) : GL ι ℂ where
  val := heisMatAt h v x₀ y t w
  inv := heisMatAt h v x₀ (-(y : InfinitePlace E → ι → ℂ)) (-t) w
  val_inv := by
    obtain ⟨hH, -, -, -, -⟩ := hyperbolic_at_place h v hp w
    rw [heisMatAt_mul hp y.2 (neg_mem y.2), heisMatAt]
    simp only [add_neg_cancel, Pi.zero_apply, Pi.sub_apply, Pi.add_apply, Pi.neg_apply,
      hForm_neg_right, Complex.neg_im, hForm_self_im hH]
    simp only [heisS, hForm_zero_left, Complex.zero_re, neg_zero, zero_div, sub_self]
    exact heisMat_zero
  inv_val := by
    obtain ⟨hH, -, -, -, -⟩ := hyperbolic_at_place h v hp w
    rw [heisMatAt_mul hp (neg_mem y.2) y.2, heisMatAt]
    simp only [neg_add_cancel, Pi.zero_apply, Pi.sub_apply, Pi.add_apply, Pi.neg_apply,
      hForm_neg_left, Complex.neg_im, hForm_self_im hH]
    simp only [heisS, hForm_zero_left, Complex.zero_re, neg_zero, zero_div, sub_self]
    exact heisMat_zero

def heisPoint (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀) : unipRadical h v x₀ :=
  ⟨⟨fun w => heisUnit hp p.1 p.2 w, mem_archUnitary.2 fun w => by
      obtain ⟨hH, -, ha, -, -⟩ := hyperbolic_at_place h v hp w
      rw [map_conj_transpose]
      exact heisMat_unitary hH ha (p.1.2 w).1 (heisS_spec hH _ _)⟩,
    mem_unipRadical.2 fun w => by
      obtain ⟨hH, -, ha, -, -⟩ := hyperbolic_at_place h v hp w
      refine ⟨heisMat_mulVec_self hH ha (p.1.2 w).1 _, fun z hz => ⟨-hForm (gramAt h v w)
        ((p.1 : InfinitePlace E → ι → ℂ) w) z, ?_⟩⟩
      change heisMat _ _ _ _ *ᵥ z = _
      rw [heisMat_mulVec, show hForm (gramAt h v w) (vecAt v x₀ w) z = 0 from hz]
      simp only [zero_smul, add_zero, neg_smul, sub_eq_add_neg]⟩

theorem heisPoint_val (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀)
    (w : InfinitePlace E) :
    ((((heisPoint hp p : unipRadical h v x₀) : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) = heisMatAt h v x₀ p.1 p.2 w := rfl


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem unipRadical_at_place (n : unipRadical h v x₀) (w : InfinitePlace E) :
    (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)ᴴ * gramAt h v w *
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = gramAt h v w ∧
    (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      vecAt v x₀ w ∧
    ∀ z, hForm (gramAt h v w) (vecAt v x₀ w) z = 0 → ∃ c : ℂ,
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z =
        z + c • vecAt v x₀ w :=
  ⟨archUnitary_at_place _ w, (mem_unipRadical.1 n.2 w).1, (mem_unipRadical.1 n.2 w).2⟩

def heisU (n : unipRadical h v x₀) (w : InfinitePlace E) : ι → ℂ :=
  (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w -
    vecAt v w₀ w

def heisYOf (n : unipRadical h v x₀) : InfinitePlace E → ι → ℂ := fun w =>
  heisU (w₀ := w₀) n w - hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w) • vecAt v x₀ w

theorem heisYOf_spec (hp : IsHyperbolicPair h x₀ w₀) (n : unipRadical h v x₀)
    (w : InfinitePlace E) :
    hForm (gramAt h v w) (vecAt v x₀ w) (heisYOf (w₀ := w₀) n w) = 0 ∧
    hForm (gramAt h v w) (vecAt v w₀ w) (heisYOf (w₀ := w₀) n w) = 0 ∧
    hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w) +
      starRingEnd ℂ (hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w)) +
      hForm (gramAt h v w) (heisYOf (w₀ := w₀) n w) (heisYOf (w₀ := w₀) n w) = 0 ∧
    (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      heisMat (gramAt h v w) (vecAt v x₀ w) (heisYOf (w₀ := w₀) n w)
        (hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w)) := by
  obtain ⟨hH, -, ha, hb, hab⟩ := hyperbolic_at_place h v hp w
  obtain ⟨hn, hna, hn'⟩ := unipRadical_at_place n w
  exact eq_heisMat hH ha hb hab hn hna hn'

def heisCoordOf (hp : IsHyperbolicPair h x₀ w₀) (n : unipRadical h v x₀) : HeisCoord h v x₀ w₀ :=
  (⟨heisYOf n, fun w => ⟨(heisYOf_spec hp n w).1, (heisYOf_spec hp n w).2.1⟩⟩,
    fun w => (hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w)).im)

end Coords

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
