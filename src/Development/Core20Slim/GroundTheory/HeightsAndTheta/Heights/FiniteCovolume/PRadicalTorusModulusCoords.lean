module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusHomeo
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusCoords
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementForm
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
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
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
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
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

section Mat

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} {a : ι → ℂ}

theorem heisMat_conj_scale {g : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) {α : ℂ}
    (hga : g *ᵥ a = α • a) {y : ι → ℂ} (hgy : g *ᵥ y = y) (s : ℂ) :
    g * heisMat H a y s =
      heisMat H a (starRingEnd ℂ α • y) ((Complex.normSq α : ℂ) * s) * g := by
  refine matrix_ext_mulVec fun z => ?_
  have h1 : hForm H a z = starRingEnd ℂ α * hForm H a (g *ᵥ z) := by
    rw [← hForm_mulVec_of_unitary H hg a z, hga, hForm_smul_left]
  have h2 : hForm H y z = hForm H y (g *ᵥ z) := by
    conv_lhs => rw [← hForm_mulVec_of_unitary H hg y z, hgy]
  rw [← mulVec_mulVec, ← mulVec_mulVec, heisMat_mulVec, heisMat_mulVec, h1, h2, hForm_smul_left,
    Complex.conj_conj, Complex.normSq_eq_conj_mul_self]
  simp only [mulVec_add, mulVec_sub, mulVec_smul, hga, hgy]
  module


omit [DecidableEq ι] in
theorem heisS_conj_smul (α : ℂ) (y : ι → ℂ) (t : ℝ) :
    heisS H (starRingEnd ℂ α • y) (Complex.normSq α * t) = (Complex.normSq α : ℂ) * heisS H y t := by
  have e : hForm H (starRingEnd ℂ α • y) (starRingEnd ℂ α • y) =
      (Complex.normSq α : ℂ) * hForm H y y := by
    rw [hForm_smul_left, hForm_smul_right, Complex.conj_conj, Complex.normSq_eq_conj_mul_self]
    ring
  apply Complex.ext
  · simp only [heisS, e, Complex.re_ofReal_mul]
    ring
  · simp only [heisS, Complex.im_ofReal_mul]

end Mat

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

def heisScale (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) (c : InfinitePlace E → ℂ) :
    heisY h v x₀ w₀ →ₗ[ℝ] heisY h v x₀ w₀ where
  toFun y := ⟨fun w => c w • (y : InfinitePlace E → ι → ℂ) w, mem_heisY.2 fun w => by
    simp only [hForm_smul_right, (y.2 w).1, (y.2 w).2, mul_zero, and_self]⟩
  map_add' y z := by
    apply Subtype.ext
    funext w
    simp [smul_add]
  map_smul' r y := by
    apply Subtype.ext
    funext w
    change c w • ((r • (y : InfinitePlace E → ι → ℂ)) w) =
      r • (c w • (y : InfinitePlace E → ι → ℂ) w)
    rw [Pi.smul_apply, real_smul_vec, real_smul_vec, smul_comm]

theorem heisPoint_torus (hp : IsHyperbolicPair h x₀ w₀) (g : archUnitary h v)
    (α : InfinitePlace E → ℂ)
    (hga : ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      α w • vecAt v x₀ w)
    (hgy : ∀ w (z : ι → ℂ), star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z)
    (p : HeisCoord h v x₀ w₀) :
    g * ((heisPoint hp p : unipRadical h v x₀) : archUnitary h v) * g⁻¹ =
      heisPoint hp (heisScale h v x₀ w₀ (fun w => starRingEnd ℂ (α w)) p.1,
        fun w => Complex.normSq (α w) * p.2 w) := by
  apply Subtype.ext
  funext w
  apply Units.ext
  have hu := archUnitary_at_place g w
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply, Units.val_mul]
  rw [heisPoint_val, heisPoint_val, heisMatAt, heisMatAt,
    heisMat_conj_scale hu (hga w) (hgy w _ (p.1.2 w).1 (p.1.2 w).2), mul_assoc, Units.mul_inv,
    mul_one]
  congr 1
  exact (heisS_conj_smul (α w) _ (p.2 w)).symm

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
