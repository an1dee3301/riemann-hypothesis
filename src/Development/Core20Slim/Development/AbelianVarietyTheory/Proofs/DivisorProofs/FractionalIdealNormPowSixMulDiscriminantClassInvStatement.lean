module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealNormPowSixMulDiscriminantClassInv
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic

@[expose] public section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdealNorm_pow_six_mul_discriminant_class_invariant : ∀ {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ), Module.finrank ℚ K = 2 → (starRingEnd ℂ).comp φK ≠ φK → ∀ (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λa Λb : PeriodPair), IsLatOf φK (𝔞 : FractionalIdeal (𝓞 K)⁰ K) Λa → IsLatOf φK (𝔟 : FractionalIdeal (𝓞 K)⁰ K) Λb → ClassGroup.mk K 𝔞 = ClassGroup.mk K 𝔟 → nrm (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λa‖ = nrm (𝔟 : FractionalIdeal (𝓞 K)⁰ K) ^ 6 * ‖latDisc Λb‖ := by
  first | exact @GlobalTheory.DiscClass.nrm_pow_mul_norm_latDisc_eq | exact GlobalTheory.DiscClass.nrm_pow_mul_norm_latDisc_eq | (intros; apply GlobalTheory.DiscClass.nrm_pow_mul_norm_latDisc_eq <;> assumption)
