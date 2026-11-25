module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.IdealLattice
public import Development.Core20Slim.Formalism.PeriodIntegrals.AreaLat
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.IdealBasisAlt
public import Development.Core20Slim.Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AreaLat
public import Development.Core20Slim.Formalism.PeriodIntegrals.LatDefs
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.NatCast
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField

namespace PI.IdealLatticeWork

theorem okBasis : OKBasis := by
  intro K _ _ h
  exact ⟨Module.finBasisOfFinrankEq ℤ (𝓞 K) (by rw [NumberField.RingOfIntegers.rank, h])⟩

theorem im_comb (u v : ℂ) (p q r s : ℤ) :
    ((starRingEnd ℂ) ((p : ℂ) * u + (q : ℂ) * v) * ((r : ℂ) * u + (s : ℂ) * v)).im
      = ((p * s - q * r : ℤ) : ℝ) * ((starRingEnd ℂ) u * v).im := by
  simp only [map_add (f := _), map_mul, map_intCast, Complex.mul_im, Complex.mul_re,
    Complex.add_im, Complex.add_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]
  push_cast
  ring

theorem im_scale (δ x y : ℂ) :
    ((starRingEnd ℂ) (δ * x) * (δ * y)).im = ‖δ‖ ^ 2 * ((starRingEnd ℂ) x * y).im := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [map_mul, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem phi_comb {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (m n : ℤ) (x y : 𝓞 K) :
    φ ((m • x + n • y : 𝓞 K) : K) = (m : ℂ) * φ (x : K) + (n : ℂ) * φ (y : K) := by
  simp [zsmul_eq_mul]

theorem assemble : Assemble := by
  intro hA hI hB hL K _ _ φ h2 hcx cc δ hcc hδ
  obtain ⟨b⟩ := hB K h2
  obtain ⟨c₁, hc₁, c₂, hc₂, hspan, p, q, r, s, hc1, hc2, hdet⟩ := hI K b cc hcc
  have hgen : AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ (c : K)} =
      AddSubgroup.closure {δ * φ (c₁ : K), δ * φ (c₂ : K)} := by
    apply le_antisymm
    · rw [AddSubgroup.closure_le]
      rintro w ⟨c, hc, rfl⟩
      obtain ⟨m, n, rfl⟩ := hspan c hc
      rw [phi_comb φ m n c₁ c₂]
      have e : δ * ((m : ℂ) * φ (c₁ : K) + (n : ℂ) * φ (c₂ : K)) =
          m • (δ * φ (c₁ : K)) + n • (δ * φ (c₂ : K)) := by
        simp only [zsmul_eq_mul]
        ring
      rw [e]
      exact AddSubgroup.add_mem _
        (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) m)
        (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) n)
    · rw [AddSubgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact AddSubgroup.subset_closure ⟨c₁, hc₁, rfl⟩
      · exact AddSubgroup.subset_closure ⟨c₂, hc₂, rfl⟩
  have hφc : ∀ c : 𝓞 K, ∀ x y : ℤ, c = x • b 0 + y • b 1 →
      φ (c : K) = (x : ℂ) * φ (b 0 : K) + (y : ℂ) * φ (b 1 : K) := by
    rintro c x y rfl
    exact phi_comb φ x y (b 0) (b 1)
  have him : ((starRingEnd ℂ) (δ * φ (c₁ : K)) * (δ * φ (c₂ : K))).im =
      ‖δ‖ ^ 2 * (((p * s - q * r : ℤ) : ℝ) * ((starRingEnd ℂ) (φ (b 0 : K)) * φ (b 1 : K)).im) := by
    rw [im_scale, hφc c₁ p q hc1, hφc c₂ r s hc2, im_comb]
  have hA' := hA K φ h2 hcx b
  have hd : (0 : ℝ) < Real.sqrt |(NumberField.discr K : ℝ)| / 2 := by
    have h0 : (NumberField.discr K : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero K
    exact div_pos (Real.sqrt_pos.mpr (abs_pos.mpr h0)) two_pos
  have hn : Ideal.absNorm cc ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hδ2 : (0 : ℝ) < ‖δ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hδ) 2
  have habs : |((starRingEnd ℂ) (δ * φ (c₁ : K)) * (δ * φ (c₂ : K))).im| =
      ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * (Real.sqrt |(NumberField.discr K : ℝ)| / 2) := by
    rw [him, abs_mul, abs_mul, hA', abs_of_pos hδ2, ← hdet, Nat.cast_natAbs, Int.cast_abs]
    ring
  have hpos : (0 : ℝ) < ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * (Real.sqrt |(NumberField.discr K : ℝ)| / 2) :=
    mul_pos (mul_pos hδ2 (by exact_mod_cast Nat.pos_of_ne_zero hn)) hd
  have hne : ((starRingEnd ℂ) (δ * φ (c₁ : K)) * (δ * φ (c₂ : K))).im ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at habs
    linarith
  refine ⟨⟨δ * φ (c₁ : K), δ * φ (c₂ : K), hne, hgen⟩, ?_⟩
  rw [hgen]
  change area (PI.lat2 _ _) = _
  rw [(hL _ _ hne).1, habs]
  ring

theorem idealLattice_of (h1 : OKArea) (h2 : IdealBasis) : PI.IdealLattice :=
  assemble h1 h2 okBasis area_lattice_formula

end PI.IdealLatticeWork
