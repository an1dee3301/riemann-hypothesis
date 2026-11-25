module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
public import Batteries.Logic
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
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
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Fourier.Notation
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open FourierTransform MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.GaussWidths

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_schwartz_gauss_width (c : ℝ) (hc : 0 < c) :
    ∃ g : SchwartzMap E ℂ, ∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
  set t : ℝ := Real.sqrt (c / Real.pi) with ht_def
  have ht : t ≠ 0 := (Real.sqrt_pos.2 (div_pos hc Real.pi_pos)).ne'
  have ht2 : t ^ 2 = c / Real.pi := Real.sq_sqrt (div_pos hc Real.pi_pos).le
  let e : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E t ht).toContinuousLinearEquiv
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (GroundTheory.Global.gaussianSchwartz E), fun y => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_exp]
  congr 1
  have hey : e y = t • y := rfl
  rw [hey, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ht2]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp

theorem mem_of_smul {M : Submodule ℂ (SchwartzMap E ℂ)} (c : ℝ) (K : ℂ) (hK : K ≠ 0)
    (u : SchwartzMap E ℂ) (hu : ∀ y, u y = K * Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)))
    (huM : u ∈ M) :
    ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M := by
  intro g hg
  have : g = K⁻¹ • u := by
    ext y
    rw [SchwartzMap.smul_apply, hu, hg, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hK, one_mul]
  rw [this]
  exact M.smul_mem _ huM

variable [MeasurableSpace E] [BorelSpace E]

theorem integral_gauss_mul_gauss (s c : ℝ) (hs : 0 < s) (hc : 0 < c) (y : E) :
    ∫ a : E, Complex.exp (-((s * ‖a‖ ^ 2 : ℝ) : ℂ)) * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) =
      ((Real.pi : ℂ) / ((s + c : ℝ) : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) *
        Complex.exp (-(((s * c / (s + c)) * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
  have hsc : 0 < s + c := by linarith
  have key : ∀ a : E, Complex.exp (-((s * ‖a‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) =
      Complex.exp (-((s + c : ℝ) : ℂ) * (‖a‖ : ℂ) ^ 2 + ((2 * c : ℝ) : ℂ) * ((inner ℝ y a : ℝ) : ℂ)) *
        Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
    intro a
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [norm_sub_sq_real]
    push_cast
    ring
  simp_rw [key]
  rw [integral_mul_const, GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (by simpa using hsc) _ y, mul_assoc, ← Complex.exp_add]
  congr 2
  have h1 : ((s + c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsc.ne'
  push_cast at h1 ⊢
  field_simp
  ring

end GlobalTheory.GaussWidths

namespace GlobalTheory.GaussWidths

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def HasWidth (M : Submodule ℂ (SchwartzMap E ℂ)) (c : ℝ) : Prop :=
  ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M

def ConvStable (M : Submodule ℂ (SchwartzMap E ℂ)) : Prop :=
  ∀ (b c : ℝ), 0 < b → 0 < c →
    (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
    ∀ (h u : SchwartzMap E ℂ),
      (∀ y, u y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
        Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) → u ∈ M

theorem cpow_ne_zero_of_pos (r : ℝ) (hr : 0 < r) (z : ℂ) : ((r : ℂ)) ^ z ≠ 0 := by
  intro h
  rw [Complex.cpow_eq_zero_iff] at h
  exact (Complex.ofReal_ne_zero.2 hr.ne') h.1

theorem hasWidth_of_lt {M : Submodule ℂ (SchwartzMap E ℂ)} (hconv : ConvStable M) (c : ℝ)
    (hc : 0 < c) (hP : HasWidth M c) (c' : ℝ) (hc' : 0 < c') (hlt : c' < c) : HasWidth M c' := by
  set s : ℝ := c * c' / (c - c') with hs_def
  have hcc : 0 < c - c' := by linarith
  have hs : 0 < s := div_pos (mul_pos hc hc') hcc
  have hsc : s * c / (s + c) = c' := by
    rw [hs_def]; field_simp; ring
  obtain ⟨h, hh⟩ := exists_schwartz_gauss_width (E := E) (s / 2) (by linarith)
  obtain ⟨g', hg'⟩ := exists_schwartz_gauss_width (E := E) c' hc'
  set K : ℂ := ((Real.pi : ℂ) / ((s + c : ℝ) : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ)
  have hK : K ≠ 0 := by
    have : (Real.pi : ℂ) / ((s + c : ℝ) : ℂ) = ((Real.pi / (s + c) : ℝ) : ℂ) := by push_cast; rfl
    simp only [K, this]
    exact cpow_ne_zero_of_pos _ (div_pos Real.pi_pos (by linarith)) _
  have huM : K • g' ∈ M := hconv (s / 2) c (by linarith) hc hP h (K • g') (fun y => by
    rw [SchwartzMap.smul_apply, smul_eq_mul, hg', ← hsc, ← integral_gauss_mul_gauss s c hs hc y]
    congr 1
    funext a
    rw [hh]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring)
  exact mem_of_smul c' K hK (K • g') (fun y => by rw [SchwartzMap.smul_apply, smul_eq_mul, hg']) huM

theorem hasWidth_fourier {M : Submodule ℂ (SchwartzMap E ℂ)} (hF : ∀ f ∈ M, 𝓕 f ∈ M) (c : ℝ)
    (hc : 0 < c) (hP : HasWidth M c) : HasWidth M (Real.pi ^ 2 / c) := by
  obtain ⟨g, hg⟩ := exists_schwartz_gauss_width (E := E) c hc
  set K : ℂ := ((Real.pi : ℂ) / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ)
  have hK : K ≠ 0 := by
    have : (Real.pi : ℂ) / (c : ℂ) = ((Real.pi / c : ℝ) : ℂ) := by push_cast; rfl
    simp only [K, this]
    exact cpow_ne_zero_of_pos _ (div_pos Real.pi_pos hc) _
  refine mem_of_smul (Real.pi ^ 2 / c) K hK (𝓕 g) (fun w => ?_) (hF g (hP g hg))
  have hfun : (g : E → ℂ) = fun v => Complex.exp (-(c : ℂ) * (‖v‖ : ℂ) ^ 2) := by
    funext v; rw [hg]; push_cast; ring_nf
  rw [SchwartzMap.fourier_coe, hfun, fourier_gaussian_innerProductSpace (by simpa using hc)]
  congr 2
  have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp

theorem hasWidth_all {M : Submodule ℂ (SchwartzMap E ℂ)} (hconv : ConvStable M)
    (hF : ∀ f ∈ M, 𝓕 f ∈ M) (hπ : HasWidth M Real.pi) (c : ℝ) (hc : 0 < c) : HasWidth M c := by
  rcases lt_trichotomy c Real.pi with hlt | heq | hgt
  · exact hasWidth_of_lt hconv Real.pi Real.pi_pos hπ c hc hlt
  · exact heq ▸ hπ
  · have hc' : 0 < Real.pi ^ 2 / c := by positivity
    have hlt : Real.pi ^ 2 / c < Real.pi := by
      rw [div_lt_iff₀ hc]; nlinarith [Real.pi_pos]
    have h1 := hasWidth_fourier hF _ hc' (hasWidth_of_lt hconv Real.pi Real.pi_pos hπ _ hc' hlt)
    have : Real.pi ^ 2 / (Real.pi ^ 2 / c) = c := by
      have := Real.pi_pos.ne'; field_simp
    rwa [this] at h1

theorem hasWidth_pi {M : Submodule ℂ (SchwartzMap E ℂ)} (G : SchwartzMap E ℂ)
    (hG : ∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) (hGM : G ∈ M) :
    HasWidth M Real.pi := by
  intro g hg
  have : g = G := by ext y; rw [hg, hG]
  rwa [this]

end GlobalTheory.GaussWidths

namespace GlobalTheory.GaussWidths

theorem all_widths_of_conv
    (hconvAll : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E]
      (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
      ∀ (b c : ℝ), 0 < b → 0 < c →
      (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
      ∀ (h u : SchwartzMap E ℂ),
        (∀ y, u y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
          Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) →
        u ∈ M) :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    (∀ f ∈ M, 𝓕 f ∈ M) →
    ∀ G : SchwartzMap E ℂ, (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ M →
    ∀ (c : ℝ), 0 < c → ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M := by
  intro E _ _ _ _ _ M hM hℓ hF G hG hGM c hc g hg
  exact hasWidth_all (fun b c' hb hc' hP h u hu => hconvAll E M hM hℓ b c' hb hc' hP h u hu) hF
    (hasWidth_pi G hG hGM) c hc g hg

end GlobalTheory.GaussWidths
