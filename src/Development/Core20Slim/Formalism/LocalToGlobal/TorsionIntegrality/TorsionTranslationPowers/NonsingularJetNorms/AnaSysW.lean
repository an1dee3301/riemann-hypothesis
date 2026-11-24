module

public import Development.Core20Slim.Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementW
public import Batteries.Logic
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bridge
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.IsTransSys
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.AnaSys
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ExistsFinitePartOneIdeleSplitCongruenceQuotient
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementA
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CompInv
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementK
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

namespace AnaSysW

open Formalism.L2.Th1

variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l])












variable {l ι W}



variable (l ι W)









abbrev xc (t : ℂ) : ℂ_[l] := ι (L.weierstrassP t) - W.b₂ / 12

abbrev yc (t : ℂ) : ℂ_[l] :=
  (ι (L.derivWeierstrassP t) - W.a₁ * (ι (L.weierstrassP t) - W.b₂ / 12) - W.a₃) / 2

variable {l L ι W}

theorem disc_ne (hU : Unif l L ι W) : W.Δ ≠ 0 := by
  intro hΔ
  have h1 := hU.1
  have h2 := hU.2
  simp only [A.g₂, A.g₃] at h1 h2
  have hc := WeierstrassCurve.c_relation W
  rw [hΔ] at hc
  apply F.discNeZero L
  apply ι.injective
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_zero]
  rw [← h1, ← h2]
  linear_combination (-1 / 1728) * hc

theorem nonsing (hU : Unif l L ι W) (t : ℂ) (ht : t ∉ L.lattice) :
    W.toAffine.Nonsingular (xc l L ι W t) (yc l L ι W t) := by
  have hΔ := disc_ne hU
  have h1 := hU.1
  have h2 := hU.2
  simp only [A.g₂, A.g₃, WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆] at h1 h2
  have hn : (curveL l L ι).toAffine.Nonsingular (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2) := by
    first
    | exact AnaSys.nonsing (l := l) (L := L) (ι := ι) t ht
    | exact AddThm.nonsing (l := l) (L := L) (ι := ι) t ht
  have he : (curveL l L ι).toAffine.Equation (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2) := by
    first
    | exact hn.1
    | exact hn.left
    | exact (WeierstrassCurve.Affine.nonsingular_iff' _ _).1 hn |>.1
  rw [WeierstrassCurve.Affine.equation_iff] at he
  simp only [curveL, A.shortW] at he
  have heq : W.toAffine.Equation (xc l L ι W t) (yc l L ι W t) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [xc, yc, WeierstrassCurve.b₂]
    linear_combination he + (ι (L.weierstrassP t) / 4) * h1 + (1 / 4) * h2
  first
  | exact WeierstrassCurve.Affine.nonsingular_of_Δ_ne_zero heq hΔ
  | (haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
     exact (WeierstrassCurve.Affine.equation_iff_nonsingular).mp heq)
  | (haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
     exact (WeierstrassCurve.Affine.equation_iff_nonsingular (W := W)).mp heq)

theorem ptW_notMem (hU : Unif l L ι W) (t : ℂ) (ht : t ∉ L.lattice) :
    ptW l L ι W t = .some _ _ (nonsing hU t ht) := by
  unfold ptW
  exact dif_pos ⟨ht, nonsing hU t ht⟩

variable (l L ι W)

theorem ptW_mem (t : ℂ) (ht : t ∈ L.lattice) : ptW l L ι W t = 0 := by
  unfold ptW
  exact dif_neg (fun h => h.1 ht)

variable {l L ι W}

theorem ptW_zero_iff (hU : Unif l L ι W) (t : ℂ) : ptW l L ι W t = 0 ↔ t ∈ L.lattice := by
  constructor
  · intro h
    by_contra ht
    rw [ptW_notMem hU t ht] at h
    first | exact WeierstrassCurve.Affine.Point.some_ne_zero _ h | simp at h | cases h | exact nomatch h
  · intro ht
    exact ptW_mem (l := l) (L := L) (ι := ι) (W := W) t ht

theorem px_ptW (hU : Unif l L ι W) (t : ℂ) (ht : t ∉ L.lattice) :
    px W (ptW l L ι W t) = xc l L ι W t := by
  rw [ptW_notMem hU t ht]
  first | rfl | simp [px]


variable (l L ι W)


def W0 : WeierstrassCurve ℂ := W.map (ι.symm : ℂ_[l] →+* ℂ)

theorem lattice_model_map : (W0 l ι W).map (ι : ℂ →+* ℂ_[l]) = W := by
  first
  | (ext <;> simp [W0])
  | (simp only [W0, WeierstrassCurve.map_map]; simp)

variable {l L ι W}

theorem lattice_model_g2 (hU : Unif l L ι W) : A.g₂ (W0 l ι W) = L.g₂ := by
  apply ι.injective
  have h := hU.1
  first
  | (simp only [A.g₂] at h ⊢; simp only [W0, WeierstrassCurve.map_c₄, map_div₀, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, map_ofNat]; exact h)
  | (simp [A.g₂, W0, map_div₀] at h ⊢; exact h)

theorem lattice_model_g3 (hU : Unif l L ι W) : A.g₃ (W0 l ι W) = L.g₃ := by
  apply ι.injective
  have h := hU.2
  first
  | (simp only [A.g₃] at h ⊢; simp only [W0, WeierstrassCurve.map_c₆, map_div₀, map_neg, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, map_ofNat]; exact h)
  | (simp [A.g₃, W0, map_div₀] at h ⊢; exact h)

theorem wpBridge (hU : Unif l L ι W) :
    A.wpReg W = PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.pSeries L) := by
  have h1 := F.curve_weierstrass_series_eq (W0 l ι W) L (lattice_model_g2 hU) (lattice_model_g3 hU)
  have h2 := (A.zMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (W0 l ι W)).2.2.1
  rw [← h1, h2, lattice_model_map]


section Trans

open F.TaylorWp

variable (L : PeriodPair) (V : WeierstrassCurve ℂ) (t : ℂ)







variable {L V}



end Trans






theorem ptW_add_lattice (hU : Unif l L ι W) (t ω : ℂ) (hω : ω ∈ L.lattice) :
    ptW l L ι W (t + ω) = ptW l L ι W t := by
  by_cases ht : t ∈ L.lattice
  · have h' : t + ω ∈ L.lattice := add_mem ht hω
    rw [ptW_mem (l := l) (L := L) (ι := ι) (W := W) _ h', ptW_mem (l := l) (L := L) (ι := ι) (W := W) _ ht]
  · have h' : t + ω ∉ L.lattice := fun h => ht (by simpa using sub_mem h hω)
    have e1 : L.weierstrassP (t + ω) = L.weierstrassP t := by
      first
      | exact L.weierstrassP_add_coe t ⟨ω, hω⟩
      | exact L.weierstrassP_add_coe ⟨ω, hω⟩ t
      | simpa using L.weierstrassP_add_coe t ⟨ω, hω⟩
    have e2 : L.derivWeierstrassP (t + ω) = L.derivWeierstrassP t := by
      first
      | exact L.derivWeierstrassP_add_coe t ⟨ω, hω⟩
      | exact L.derivWeierstrassP_add_coe ⟨ω, hω⟩ t
      | simpa using L.derivWeierstrassP_add_coe t ⟨ω, hω⟩
    rw [ptW_notMem hU _ h', ptW_notMem hU _ ht, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨by simp only [xc, e1], by simp only [yc, e1, e2]⟩

theorem ptW_neg (hU : Unif l L ι W) (t : ℂ) : ptW l L ι W (-t) = -ptW l L ι W t := by
  by_cases ht : t ∈ L.lattice
  · have ht' : -t ∈ L.lattice := neg_mem ht
    rw [ptW_mem (l := l) (L := L) (ι := ι) (W := W) _ ht', ptW_mem (l := l) (L := L) (ι := ι) (W := W) _ ht]
    first | simp | rfl | exact neg_zero.symm
  · have ht' : -t ∉ L.lattice := fun h => ht (by simpa using neg_mem h)
    rw [ptW_notMem hU _ ht', ptW_notMem hU _ ht, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    first
    | (refine ⟨?_, ?_⟩ <;> simp [xc, yc, WeierstrassCurve.Affine.negY, PeriodPair.weierstrassP_neg, PeriodPair.derivWeierstrassP_neg] <;> ring)
    | (refine ⟨?_, ?_⟩ <;> simp [xc, yc, WeierstrassCurve.Affine.negY, L.weierstrassP_neg, L.derivWeierstrassP_neg] <;> ring)

section Law

variable [DecidableEq ℂ_[l]]

theorem ptW_add_generic (hU : Unif l L ι W) (s t : ℂ) (hs : s ∉ L.lattice) (ht : t ∉ L.lattice)
    (hp : s + t ∉ L.lattice) (hm : s - t ∉ L.lattice) :
    ptW l L ι W (s + t) = ptW l L ι W s + ptW l L ι W t := by
  have hne := AddThm.P_sub_ne L s t hs ht hp hm
  have hne' : ι (L.weierstrassP s) - ι (L.weierstrassP t) ≠ 0 := by
    rw [← map_sub]
    exact fun h => hne (ι.injective (h.trans (map_zero ι).symm))
  have hd : xc l L ι W s - xc l L ι W t = ι (L.weierstrassP s) - ι (L.weierstrassP t) := by
    simp only [xc]
    ring
  have hx : xc l L ι W s ≠ xc l L ι W t := sub_ne_zero.1 (by rw [hd]; exact hne')
  have hX := congrArg ι (AddThm.P_add L s t hs ht hp hm)
  have hY := congrArg ι (AddThm.collinear L s t hs ht hp)
  simp only [map_pow, map_sub, map_mul, map_add (f := _), map_neg, map_div₀, map_ofNat] at hX hY
  rw [ptW_notMem hU s hs, ptW_notMem hU t ht, ptW_notMem hU _ hp,
    WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  have e1 : xc l L ι W (s + t) =
      W.toAffine.addX (xc l L ι W s) (xc l L ι W t)
        (W.toAffine.slope (xc l L ι W s) (xc l L ι W t) (yc l L ι W s) (yc l L ι W t)) := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx, hd]
    simp only [WeierstrassCurve.Affine.addX, xc, yc, WeierstrassCurve.b₂]
    rw [hX]
    field_simp
    ring
  have e2 : yc l L ι W (s + t) =
      W.toAffine.addY (xc l L ι W s) (xc l L ι W t) (yc l L ι W s)
        (W.toAffine.slope (xc l L ι W s) (xc l L ι W t) (yc l L ι W s) (yc l L ι W t)) := by
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, ← e1,
      WeierstrassCurve.Affine.slope_of_X_ne hx, hd]
    simp only [WeierstrassCurve.Affine.negY, xc, yc]
    field_simp
    linear_combination 144 * hY
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨e1, e2⟩

theorem ptW_add (hU : Unif l L ι W) (s t : ℂ) :
    ptW l L ι W (s + t) = ptW l L ι W s + ptW l L ι W t := by
  by_cases hs : s ∈ L.lattice
  · rw [add_comm s t, ptW_add_lattice hU t s hs, ptW_mem l L ι W s hs, zero_add]
  by_cases ht : t ∈ L.lattice
  · rw [ptW_add_lattice hU s t ht, ptW_mem l L ι W t ht, add_zero]
  by_cases hp : s + t ∈ L.lattice
  · have h : ptW l L ι W t = -ptW l L ι W s := by
      rw [← ptW_neg hU, ← ptW_add_lattice hU (-s) (s + t) hp]
      congr 1
      ring
    rw [ptW_mem l L ι W _ hp, h, add_neg_cancel]
  by_cases hm : s - t ∈ L.lattice
  · have h1 : ptW l L ι W s = ptW l L ι W t := by
      rw [← ptW_add_lattice hU t (s - t) hm]
      congr 1
      ring
    have h2 : ptW l L ι W (s + t) = ptW l L ι W (t + t) := by
      rw [← ptW_add_lattice hU (t + t) (s - t) hm]
      congr 1
      ring
    have htt : t + t ∉ L.lattice := fun h => hp (by
      have := L.lattice.add_mem h hm
      convert this using 1
      ring)
    obtain ⟨u, hu2, hup, hum⟩ := AddThm.exists_finite_part_one_idele_split_congruence_quotient L t
    have hu : u ∉ L.lattice := fun h => hu2 (by
      rw [two_mul]
      exact L.lattice.add_mem h h)
    have hu' : -u ∉ L.lattice := fun h => hu (by simpa using L.lattice.neg_mem h)
    have a1 : ptW l L ι W ((t + u) + (t - u)) = ptW l L ι W (t + u) + ptW l L ι W (t - u) :=
      ptW_add_generic hU _ _ hup hum (by convert htt using 2; ring) (by convert hu2 using 2; ring)
    have a2 : ptW l L ι W (t + u) = ptW l L ι W t + ptW l L ι W u :=
      ptW_add_generic hU _ _ ht hu hup hum
    have a3 : ptW l L ι W (t + -u) = ptW l L ι W t + ptW l L ι W (-u) :=
      ptW_add_generic hU _ _ ht hu' (by rwa [← sub_eq_add_neg]) (by rwa [sub_neg_eq_add])
    rw [h2, h1]
    have e : t + t = (t + u) + (t - u) := by ring
    rw [e, a1, a2, sub_eq_add_neg, a3, ptW_neg hU]
    abel
  exact ptW_add_generic hU s t hs ht hp hm

end Law

end AnaSysW

theorem analytic_point_eq_zero_iff : PtWZero := by
  intro l _ L ι W hU t
  exact AnaSysW.ptW_zero_iff hU t


open Classical in
theorem analytic_point_map_add : PtWAdd := by
  intro l _ L ι W hU s t
  exact AnaSysW.ptW_add hU s t




end Formalism.L2.Th1.E
