module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DensDefs
public import Batteries.Logic
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundAlt
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Init.Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ}

def gK (v : E n) : ℝ := ∏ a, ∏ b, (Real.sqrt Real.pi)⁻¹ * Real.exp (-(v a b) ^ 2)

theorem gK_nonneg (v : E n) : 0 ≤ gK v := by
  unfold gK
  exact Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b _ =>
    mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.exp_pos _).le

theorem integrable_gK : Integrable (gK (n := n)) := by
  have h1 : Integrable (fun s : ℝ => (Real.sqrt Real.pi)⁻¹ * Real.exp (-s ^ 2)) := by
    have := (integrable_exp_neg_mul_sq (b := 1) one_pos).const_mul (Real.sqrt Real.pi)⁻¹
    simpa using this
  have h2 : Integrable (fun w : Fin n → ℝ => ∏ b, (Real.sqrt Real.pi)⁻¹ * Real.exp (-(w b) ^ 2)) :=
    Integrable.fintype_prod (f := fun _ (s : ℝ) => (Real.sqrt Real.pi)⁻¹ * Real.exp (-s ^ 2)) (fun _ => h1)
  exact Integrable.fintype_prod (f := fun _ (w : Fin n → ℝ) => ∏ b, (Real.sqrt Real.pi)⁻¹ * Real.exp (-(w b) ^ 2))
    (fun _ => h2)

theorem integral_gK : ∫ v, gK (n := n) v = 1 := by
  have h1 : ∫ s : ℝ, (Real.sqrt Real.pi)⁻¹ * Real.exp (-s ^ 2) = 1 := by
    rw [integral_const_mul]
    have := integral_gaussian 1
    simp only [neg_mul, one_mul, div_one] at this
    rw [this]
    exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  unfold gK
  rw [integral_fintype_prod_volume_eq_prod (f := fun _ (w : Fin n → ℝ) =>
    ∏ b, (Real.sqrt Real.pi)⁻¹ * Real.exp (-(w b) ^ 2))]
  simp_rw [integral_fintype_prod_volume_eq_prod (f := fun _ (s : ℝ) => (Real.sqrt Real.pi)⁻¹ * Real.exp (-s ^ 2)), h1,
    Finset.prod_const_one]

theorem gauss_prod (ε : ℝ) (y : E n) :
    Complex.exp (-((ε * ip y y : ℝ) : ℂ)) = ∏ a, ∏ b, Complex.exp (-(ε : ℂ) * ((y a b : ℝ) : ℂ) ^ 2) := by
  simp_rw [← Complex.exp_sum]
  congr 1
  unfold ip
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem integrable_gauss (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun y : E n => Complex.exp (-((ε * ip y y : ℝ) : ℂ))) := by
  simp_rw [gauss_prod]
  have h1 : Integrable (fun s : ℝ => Complex.exp (-(ε : ℂ) * (s : ℂ) ^ 2)) :=
    integrable_cexp_neg_mul_sq (by simpa using hε)
  have h2 : Integrable (fun w : Fin n → ℝ => ∏ b, Complex.exp (-(ε : ℂ) * ((w b : ℝ) : ℂ) ^ 2)) :=
    Integrable.fintype_prod (f := fun _ (s : ℝ) => Complex.exp (-(ε : ℂ) * (s : ℂ) ^ 2)) (fun _ => h1)
  exact Integrable.fintype_prod (f := fun _ (w : Fin n → ℝ) => ∏ b, Complex.exp (-(ε : ℂ) * ((w b : ℝ) : ℂ) ^ 2))
    (fun _ => h2)

theorem norm_gauss_le (ε : ℝ) (hε : 0 < ε) (y : E n) : ‖Complex.exp (-((ε * ip y y : ℝ) : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have h : 0 ≤ ip y y := by
    unfold ip
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => mul_self_nonneg _
  have : (-((ε * ip y y : ℝ) : ℂ)).re = -(ε * ip y y) := by simp
  rw [this, Real.exp_le_one_iff]
  nlinarith

theorem kraw_eq (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : t ≠ 0) (u : E n) :
    (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) *
        ∫ y : E n, Complex.exp (-((ε * ip y y : ℝ) : ℂ)) * Complex.exp (Complex.I * t * ip y u) =
      (((|t| / (2 * Real.sqrt ε)) ^ (n ^ 2) * gK ((|t| / (2 * Real.sqrt ε)) • u) : ℝ) : ℂ) := by
  set lam : ℝ := |t| / (2 * Real.sqrt ε) with hlam
  have hε' : 0 < (ε : ℂ).re := by simpa using hε

  have hprod : ∀ y : E n, Complex.exp (-((ε * ip y y : ℝ) : ℂ)) * Complex.exp (Complex.I * t * ip y u) =
      ∏ a, ∏ b, (Complex.exp (Complex.I * ((t * u a b : ℝ) : ℂ) * ((y a b : ℝ) : ℂ)) *
        Complex.exp (-(ε : ℂ) * ((y a b : ℝ) : ℂ) ^ 2)) := by
    intro y
    simp_rw [Finset.prod_mul_distrib, ← gauss_prod, ← Complex.exp_sum]
    rw [mul_comm]
    congr 2
    unfold ip
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hint : ∫ y : E n, Complex.exp (-((ε * ip y y : ℝ) : ℂ)) * Complex.exp (Complex.I * t * ip y u) =
      ∏ a, ∏ b, ((Real.pi : ℂ) / ε) ^ (1 / 2 : ℂ) * Complex.exp (-((t * u a b : ℝ) : ℂ) ^ 2 / (4 * ε)) := by
    simp_rw [hprod]
    rw [integral_fintype_prod_volume_eq_prod (f := fun a (w : Fin n → ℝ) =>
      ∏ b, (Complex.exp (Complex.I * ((t * u a b : ℝ) : ℂ) * ((w b : ℝ) : ℂ)) *
        Complex.exp (-(ε : ℂ) * ((w b : ℝ) : ℂ) ^ 2)))]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [integral_fintype_prod_volume_eq_prod (f := fun b (s : ℝ) =>
      Complex.exp (Complex.I * ((t * u a b : ℝ) : ℂ) * (s : ℂ)) * Complex.exp (-(ε : ℂ) * (s : ℂ) ^ 2))]
    refine Finset.prod_congr rfl fun b _ => ?_
    exact fourierIntegral_gaussian hε' _

  have hsq : ((Real.pi : ℂ) / ε) ^ (1 / 2 : ℂ) = ((Real.sqrt Real.pi / Real.sqrt ε : ℝ) : ℂ) := by
    rw [← Real.sqrt_div' _ hε.le, Real.sqrt_eq_rpow, Complex.ofReal_cpow (div_nonneg Real.pi_pos.le hε.le)]
    push_cast
    ring_nf
  have hcoord : ∀ s : ℝ, (((|t| / (2 * Real.pi)) : ℝ) : ℂ) * (((Real.pi : ℂ) / ε) ^ (1 / 2 : ℂ) *
      Complex.exp (-((t * s : ℝ) : ℂ) ^ 2 / (4 * ε))) =
      ((lam * ((Real.sqrt Real.pi)⁻¹ * Real.exp (-(lam * s) ^ 2)) : ℝ) : ℂ) := by
    intro s
    have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hse : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have hee : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
    have hpp : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
    rw [hsq]
    have hexp : (-((t * s : ℝ) : ℂ) ^ 2 / (4 * ε)) = ((-(lam * s) ^ 2 : ℝ) : ℂ) := by
      rw [hlam]
      push_cast
      have : ((|t| : ℝ) : ℂ) ^ 2 = (t : ℂ) ^ 2 := by
        rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
      have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
      have hs0 : ((Real.sqrt ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hse.ne'
      have hee' : ((Real.sqrt ε : ℝ) : ℂ) ^ 2 = (ε : ℂ) := by exact_mod_cast hee
      field_simp
      rw [this, hee']
      ring
    rw [hexp, ← Complex.ofReal_exp]
    push_cast
    rw [hlam]
    have hpi0 : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
    have hs0 : ((Real.sqrt ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hse.ne'
    have hpp' : ((Real.sqrt Real.pi : ℝ) : ℂ) ^ 2 = (Real.pi : ℂ) := by exact_mod_cast hpp
    have hpi1 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    push_cast
    field_simp
    rw [← hpp']
  rw [hint]
  have hC : (((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) = ∏ _a : Fin n, ∏ _b : Fin n, (((|t| / (2 * Real.pi)) : ℝ) : ℂ) := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    rw [← pow_mul, sq]
  rw [hC, ← Finset.prod_mul_distrib]
  simp_rw [← Finset.prod_mul_distrib, hcoord]
  push_cast
  unfold gK
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [show ((lam : ℂ)) ^ (n ^ 2) = ∏ _a : Fin n, ∏ _b : Fin n, (lam : ℂ) by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul, sq]]
  rw [← Finset.prod_mul_distrib]
  simp_rw [← Finset.prod_mul_distrib]

end PositivityTheory.Rg.Sw.WR.D.Moll
