module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstIsogeny
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.HasSecondLogDeriv
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM (omegaK HasCMBy)

namespace Formalism.L2.Th1.F

namespace CmBy

private lemma re_add_mul_omegaK (d : ℕ) (m n : ℤ) :
    ((m : ℂ) + (n : ℂ) * omegaK d).re = (m : ℝ) + (n : ℝ) / 2 := by
  simp [omegaK]
  ring

private lemma im_add_mul_omegaK (d : ℕ) (m n : ℤ) :
    ((m : ℂ) + (n : ℂ) * omegaK d).im = (n : ℝ) * Real.sqrt d / 2 := by
  simp [omegaK]
  ring

lemma normSq_omega (d : ℕ) (m n : ℤ) :
    Complex.normSq ((m : ℂ) + (n : ℂ) * omegaK d)
      = (m : ℝ) ^ 2 + (m : ℝ) * (n : ℝ) + (n : ℝ) ^ 2 * ((1 + (d : ℝ)) / 4) := by
  have hs : Real.sqrt (d : ℝ) * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  rw [Complex.normSq_apply, re_add_mul_omegaK, im_add_mul_omegaK]
  linear_combination ((n : ℝ) ^ 2 / 4) * hs

lemma ne_zero (d : ℕ) (hd : 0 < d) (m n : ℤ) (h : (m, n) ≠ (0, 0)) :
    (m : ℂ) + (n : ℂ) * omegaK d ≠ 0 := by
  intro h0
  have hre := re_add_mul_omegaK d m n
  have him := im_add_mul_omegaK d m n
  rw [h0, Complex.zero_re] at hre
  rw [h0, Complex.zero_im] at him
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hn : (n : ℝ) = 0 := by
    have h2 : (n : ℝ) * Real.sqrt d = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact h1
    · linarith
  have hm : (m : ℝ) = 0 := by rw [hn] at hre; linarith
  have hn' : n = 0 := by exact_mod_cast hn
  have hm' : m = 0 := by exact_mod_cast hm
  exact h (by rw [hm', hn'])

end CmBy

theorem has_cm_stable : HasCMByStable := by
  intro d L hL m n
  refine ⟨?_, CmBy.normSq_omega d m n⟩
  intro w hw
  have h1 : omegaK d * w ∈ L.lattice := hL w hw
  have he : ((m : ℂ) + (n : ℂ) * omegaK d) * w = m • w + n • (omegaK d * w) := by
    simp only [zsmul_eq_mul]; ring
  rw [he]
  exact L.lattice.add_mem (L.lattice.smul_mem m hw) (L.lattice.smul_mem n h1)

theorem hasCMByScale_of (h : Homogeneity) : HasCMByScale := by
  intro d L c hc hL w hw
  have hmem := (h L c hc).1
  rw [hmem] at hw ⊢
  rw [show c⁻¹ * (omegaK d * w) = omegaK d * (c⁻¹ * w) by ring]
  exact hL _ hw


theorem hasCMByIsogeny_of (hs : HasCMByStable) (he : KerRepsExist) (hc : KerRepsCard)
    (hf : IsogenyFormulaInstance) (h2 : QuasiPeriodConstIsogeny) : HasCMByIsogeny := by
  intro d L hL m n hmn hd
  have hα0 := CmBy.ne_zero d hd m n hmn
  obtain ⟨hms, hnorm⟩ := hs d L hL m n
  obtain ⟨S, hS⟩ := he L _ hα0 hms
  exact ⟨S, hS, (hc L _ S hα0 hms hS).trans hnorm, hf L _ S hα0 hms hS, h2 L _ S hα0 hms hS⟩


theorem has_cm_scale : HasCMByScale := hasCMByScale_of homogeneity


theorem hasCMByIsogeny_of' (hf : IsogenyFormulaInstance) : HasCMByIsogeny :=
  hasCMByIsogeny_of has_cm_stable kerRepsExist kerRepsCard hf quasiPeriodConstIsogeny


end Formalism.L2.Th1.F
