module

public import Mathlib
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Development.Core20Slim.ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Dvd
public import Init.Data.Zero
public import Init.Ext
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem coeff_xp {R : Type*} [CommRing R] (k : ℕ) (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (xp k f) = if k ∣ n then PowerSeries.coeff (n / k) f else 0 := by
  rw [xp, PowerSeries.coeff_mk]








theorem CoeffIn.map_int (R : Subring ℂ) (f : PowerSeries ℤ) : CoeffIn R (f.map (Int.castRingHom ℂ)) := by
  intro n
  rw [PowerSeries.coeff_map, eq_intCast]
  exact intCast_mem R _


theorem CoeffIn.sub {R : Subring ℂ} {f g : PowerSeries ℂ} (hf : CoeffIn R f) (hg : CoeffIn R g) :
    CoeffIn R (f - g) := by
  intro n
  rw [map_sub]
  exact sub_mem (hf n) (hg n)

theorem CoeffIn.mul {R : Subring ℂ} {f g : PowerSeries ℂ} (hf : CoeffIn R f) (hg : CoeffIn R g) :
    CoeffIn R (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun p _ => mul_mem (hf _) (hg _)

theorem CoeffIn.one (R : Subring ℂ) : CoeffIn R 1 := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact one_mem R
  · exact zero_mem R


theorem CoeffIn.xp {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) (k : ℕ) : CoeffIn R (xp k f) := by
  intro n
  rw [coeff_xp]
  split_ifs
  · exact hf _
  · exact zero_mem R

theorem CoeffIn.sub1 {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) {c : ℂ} (hc : c ∈ R) (k : ℕ) :
    CoeffIn R (sub1 c k f) := by
  have hr : ReciprocityTheory.ChartRestriction.L1.CoeffIn R (PowerSeries.rescale c f) := fun m => by
    rw [PowerSeries.coeff_rescale]
    exact mul_mem (pow_mem hc m) (hf m)
  exact ReciprocityTheory.ChartRestriction.L1.CoeffIn.xp hr k

theorem LowUnit.mul {R : Subring ℂ} {f g : PowerSeries ℂ} {n n' : ℕ} {u u' : ℂ} (hf : LowUnit R f n u)
    (hg : LowUnit R g n' u') : LowUnit R (f * g) (n + n') (u * u') := by
  obtain ⟨hu, hui, hu0, hlow, hc⟩ := hf
  obtain ⟨hu', hui', hu0', hlow', hc'⟩ := hg
  refine ⟨mul_mem hu hu', by rw [mul_inv]; exact mul_mem hui hui', mul_ne_zero hu0 hu0', ?_, ?_⟩
  · intro m hm
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases h1 : p.1 < n
    · rw [hlow _ h1, zero_mul]
    · rw [hlow' _ (by omega), mul_zero]
  · rw [PowerSeries.coeff_mul, Finset.sum_eq_single (n, n')]
    · rw [hc, hc']
    · intro p hp hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_cases h1 : p.1 < n
      · rw [hlow _ h1, zero_mul]
      · have h2 : p.2 < n' := by
          by_contra h2
          exact hne (Prod.ext (by show p.1 = n; omega) (by show p.2 = n'; omega))
        rw [hlow' _ h2, mul_zero]
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (rfl : n + n' = n + n')) h

theorem LowUnit.one (R : Subring ℂ) : LowUnit R 1 0 1 := by
  refine ⟨one_mem R, by rw [inv_one]; exact one_mem R, one_ne_zero,
    fun n hn => absurd hn (Nat.not_lt_zero n), ?_⟩
  simp

theorem LowUnit.prod {R : Subring ℂ} {α : Type*} (s : Finset α) (f : α → PowerSeries ℂ)
    (hf : ∀ t ∈ s, ∃ n u, LowUnit R (f t) n u) : ∃ n u, LowUnit R (∏ t ∈ s, f t) n u := Finset.prod_induction f (fun g => ∃ n u, ReciprocityTheory.ChartRestriction.L1.LowUnit R g n u)
    (fun a b ⟨n, u, ha⟩ ⟨n', u', hb⟩ => ⟨n + n', u * u', ReciprocityTheory.ChartRestriction.L1.LowUnit.mul ha hb⟩)
    ⟨0, 1, ReciprocityTheory.ChartRestriction.L1.LowUnit.one R⟩ hf

end ReciprocityTheory.ChartRestriction.L1
