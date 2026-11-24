module

public import Mathlib
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.AdelicFourier2TensorCosetIndicatorAlgebraMap
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.GlobalZeta
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeChar
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.IdeleMeasure
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic.GodementSection

open GroundTheory.Global GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.Reduction IdeleGroup

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def modPow (x : IdeleGroup K) (s : ℂ) : ℂ := ((ideleModule K x : ℝ) : ℂ) ^ s

theorem modPow_mul (x y : IdeleGroup K) (s : ℂ) : modPow (x * y) s = modPow x s * modPow y s := by
  simp only [modPow, map_mul, Positive.val_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (ideleModule K x).2.le (ideleModule K y).2.le s

theorem modPow_add (x : IdeleGroup K) (s t : ℂ) : modPow x (s + t) = modPow x s * modPow x t :=
  Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (ideleModule K x).2.ne')

theorem modPow_one (s : ℂ) : modPow (1 : IdeleGroup K) s = 1 := by
  simp [modPow]

theorem modPow_ne_zero (x : IdeleGroup K) (s : ℂ) : modPow x s ≠ 0 := by
  simp [modPow, (ideleModule K x).2.ne']




theorem globalZeta_mul_right (F : 𝔸[K] → ℂ) (μ : HeckeCharacter K) (s : ℂ) (d : IdeleGroup K) :
    globalZeta (fun t ↦ F (t * (d : 𝔸[K]))) μ s =
      (((μ.toIdele d)⁻¹ : Circle) : ℂ) * modPow d (-s) * globalZeta F μ s := by
  set G : IdeleGroup K → ℂ := fun x ↦ F x * (μ.toIdele x : ℂ) * modPow x s with hG
  have hpt : ∀ x : IdeleGroup K, F ((x : 𝔸[K]) * d) * (μ.toIdele x : ℂ) * modPow x s =
      (((μ.toIdele d)⁻¹ : Circle) : ℂ) * modPow d (-s) * G (x * d) := by
    intro x
    have h1 : modPow d (-s) * modPow d s = 1 := by
      rw [← modPow_add, neg_add_cancel]; simp [modPow]
    have h2 : (((μ.toIdele d)⁻¹ : Circle) : ℂ) * (μ.toIdele d : ℂ) = 1 := by
      rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
    simp only [hG, Units.val_mul, map_mul, Circle.coe_mul, modPow_mul]
    linear_combination (-(F ((x : 𝔸[K]) * d) * (μ.toIdele x : ℂ) * modPow x s)) *
      ((((μ.toIdele d)⁻¹ : Circle) : ℂ) * (μ.toIdele d : ℂ) * h1 + h2)
  have : globalZeta (fun t ↦ F (t * (d : 𝔸[K]))) μ s =
      ∫ x, (((μ.toIdele d)⁻¹ : Circle) : ℂ) * modPow d (-s) * G (x * d) ∂ideleMeasure K := by
    simp only [globalZeta]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ hpt x)
  rw [this, integral_const_mul]
  simp_rw [mul_comm _ d]
  rw [integral_mul_left_eq_self G d]
  rfl



end

end GroundTheory.Automorphic.GodementSection
