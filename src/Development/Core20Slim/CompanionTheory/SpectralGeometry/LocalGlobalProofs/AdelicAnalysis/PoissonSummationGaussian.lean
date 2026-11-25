module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.PoiLat

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem quad_mulVec (P : Matrix κ κ ℝ) (W : Matrix κ κ ℂ) (v : κ → ℝ) :
    (fun i => (((P *ᵥ v) i : ℝ) : ℂ)) ⬝ᵥ (W *ᵥ fun i => (((P *ᵥ v) i : ℝ) : ℂ)) =
      (fun i => (v i : ℂ)) ⬝ᵥ
        (((P.map Complex.ofReal)ᵀ * W * P.map Complex.ofReal) *ᵥ fun i => (v i : ℂ)) := by
  rw [GlobalTheory.ofReal_mulVec_eq, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (fun i => (v i : ℂ)) ((P.map Complex.ofReal)ᵀ), Matrix.vecMul_transpose]

theorem contragredient_congr {g : Matrix κ κ ℝ} (hg : g.det ≠ 0) (Z : Matrix κ κ ℂ) :
    (((g⁻¹)ᵀ).map Complex.ofReal)ᵀ * Z⁻¹ * ((g⁻¹)ᵀ).map Complex.ofReal =
      ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹ := by
  have hC : (g⁻¹).map Complex.ofReal = (g.map Complex.ofReal)⁻¹ := (GlobalTheory.inv_map_ofReal hg).symm
  have hC' : ((g⁻¹)ᵀ).map Complex.ofReal = ((g.map Complex.ofReal)⁻¹)ᵀ := by
    rw [Matrix.transpose_map, hC]
  rw [hC', Matrix.transpose_transpose, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.transpose_nonsing_inv, Matrix.mul_assoc]

theorem gaussian_lattice_term (Z : Matrix κ κ ℂ) {g : Matrix κ κ ℝ} (hg : g.det ≠ 0)
    (a : κ → ℝ) (n : κ → ℤ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I *
        ((fun i => (((a + g *ᵥ fun i => (n i : ℝ)) i : ℝ) : ℂ)) ⬝ᵥ
          (Z *ᵥ fun i => (((a + g *ᵥ fun i => (n i : ℝ)) i : ℝ) : ℂ)))) =
      GlobalTheory.riemannThetaTerm (g⁻¹ *ᵥ a) 0
        ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal) 0 n := by
  have hv : a + g *ᵥ (fun i => (n i : ℝ)) = g *ᵥ ((fun i => (n i : ℝ)) + g⁻¹ *ᵥ a) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hg),
      Matrix.one_mulVec, add_comm]
  have hs : (fun i => ((((fun i => (n i : ℝ)) + g⁻¹ *ᵥ a) i : ℝ) : ℂ)) =
      ReciprocityTheory.PTheta.shiftVec (g⁻¹ *ᵥ a) n := by
    funext i
    simp [ReciprocityTheory.PTheta.shiftVec]
  have h0 : (0 : κ → ℂ) + ReciprocityTheory.PTheta.ofRealVec (0 : κ → ℝ) = 0 := by
    funext i
    simp [ReciprocityTheory.PTheta.ofRealVec]
  rw [hv, quad_mulVec, hs]
  simp only [GlobalTheory.riemannThetaTerm, ReciprocityTheory.PTheta.thetaTerm, ReciprocityTheory.PTheta.eC]
  rw [h0, dotProduct_zero, add_zero]
  congr 1
  ring

theorem gaussian_fourier {Z : Matrix κ κ ℂ} (hZ : GlobalTheory.IsSiegel Z) (y : κ → ℝ) :
    ∫ x : κ → ℝ, Complex.exp ((Real.pi : ℂ) * Complex.I *
        ((fun i => (x i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (x i : ℂ)))) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ y : ℝ) : ℂ)) =
      GlobalTheory.siegelGaussIntegral Z * Complex.exp (-((Real.pi : ℂ) * Complex.I) *
        ((fun i => (y i : ℂ)) ⬝ᵥ (Z⁻¹ *ᵥ fun i => (y i : ℂ)))) := by
  have hq := hZ.integral_cexp_quadratic (fun i => (y i : ℂ))
  rw [← hq]
  congr 1
  funext x
  rw [← Complex.exp_add]
  congr 1
  have hxy : ((x ⬝ᵥ y : ℝ) : ℂ) = (fun i => (x i : ℂ)) ⬝ᵥ (fun i => (y i : ℂ)) := by
    simp [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [hxy]
  ring

theorem siegelGaussIntegral_congr (Z : Matrix κ κ ℂ) {g : Matrix κ κ ℝ} (hg : g.det ≠ 0) :
    GlobalTheory.siegelGaussIntegral ((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal) =
      ((|g.det|⁻¹ : ℝ) : ℂ) * GlobalTheory.siegelGaussIntegral Z := by
  have hv : Continuous fun y : κ → ℝ => fun i => (y i : ℂ) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
  have hf : Continuous fun y : κ → ℝ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((fun i => (y i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (y i : ℂ)))) :=
    Complex.continuous_exp.comp (continuous_const.mul (hv.dotProduct (continuous_const.matrix_mulVec hv)))
  have key := GlobalTheory.integral_comp_mulVec_of_det_ne_zero hg hf
  simp only [quad_mulVec] at key
  simp only [GlobalTheory.siegelGaussIntegral]
  rw [← abs_inv]
  exact key

theorem fourier_lattice_term {Z : Matrix κ κ ℂ} (hZ : GlobalTheory.IsSiegel Z) {g : Matrix κ κ ℝ}
    (hg : g.det ≠ 0) (n : κ → ℤ) :
    Complex.exp (-((Real.pi : ℂ) * Complex.I) *
        ((fun i => ((((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) i : ℝ) : ℂ)) ⬝ᵥ
          (Z⁻¹ *ᵥ fun i => ((((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) i : ℝ) : ℂ)))) =
      GlobalTheory.riemannThetaTerm 0 0 (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by
  have h0 : (0 : κ → ℂ) + ReciprocityTheory.PTheta.ofRealVec (0 : κ → ℝ) = 0 := by
    funext i
    simp [ReciprocityTheory.PTheta.ofRealVec]
  have hs : ReciprocityTheory.PTheta.shiftVec (0 : κ → ℝ) n = fun i => (((n i : ℝ)) : ℂ) := by
    funext i
    simp [ReciprocityTheory.PTheta.shiftVec]
  rw [quad_mulVec, contragredient_congr hg]
  simp only [GlobalTheory.riemannThetaTerm, ReciprocityTheory.PTheta.thetaTerm, ReciprocityTheory.PTheta.eC]
  rw [h0, dotProduct_zero, add_zero, hs, Matrix.neg_mulVec, dotProduct_neg]
  congr 1
  ring

theorem phase_lattice {g : Matrix κ κ ℝ} (a : κ → ℝ) (n : κ → ℤ) :
    ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ) =
      (fun i => (n i : ℂ)) ⬝ᵥ fun i => ((g⁻¹ *ᵥ a) i : ℂ) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp only [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _


end GlobalTheory.CompanionTheory.SW.Core.PoiLat
