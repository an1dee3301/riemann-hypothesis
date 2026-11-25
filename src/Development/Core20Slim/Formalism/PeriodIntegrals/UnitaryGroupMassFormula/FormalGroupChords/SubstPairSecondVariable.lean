module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.FglChordFactor
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.SubstMem
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.FormalGroupLawExists
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Preorder.Finsupp
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Classical

namespace PI.FglChordFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS subst_mem_SerS subst_psubst)

variable {p : ℕ} [Fact p.Prime]

theorem hasSubst2 {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hu : MvPowerSeries.constantCoeff u = 0)
    (hv : MvPowerSeries.constantCoeff v = 0) : MvPowerSeries.HasSubst ![u, v] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.2 ⟨by simpa using hu, by simpa using hv⟩)

theorem subst_pair_first_variable {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) :
    MvPowerSeries.subst ![u, v] (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) = u := by
  rw [MvPowerSeries.subst_X hs]; simp

theorem subst_pair_second_variable {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) :
    MvPowerSeries.subst ![u, v] (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) = v := by
  rw [MvPowerSeries.subst_X hs]; simp

theorem subst_pair_first_series {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst ![u, v] (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) f) =
      PowerSeries.subst u f := by
  rw [subst_psubst (PowerSeries.HasSubst.X 0) hs, subst_pair_first_variable hs]

theorem subst_pair_second_series {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst ![u, v] (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) f) =
      PowerSeries.subst v f := by
  rw [subst_psubst (PowerSeries.HasSubst.X 1) hs, subst_pair_second_variable hs]

theorem subst_pair_comp {u v u' v' : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v])
    (hs' : MvPowerSeries.HasSubst ![u', v']) (H : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.subst ![u, v] (MvPowerSeries.subst ![u', v'] H) =
      MvPowerSeries.subst ![MvPowerSeries.subst ![u, v] u', MvPowerSeries.subst ![u, v] v'] H := by
  rw [MvPowerSeries.subst_comp_subst_apply hs' hs]
  congr 1
  funext i
  fin_cases i <;> simp

theorem subst_pair_variables_self (H : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] H = H := by
  have e : ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1] = MvPowerSeries.X := by
    funext i; fin_cases i <;> simp
  rw [e, MvPowerSeries.subst_self]; rfl

theorem X_mem_SerS (S : Subring ℂ_[p]) (i : Fin 2) :
    (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[p]) ∈ SerS S (Fin 2) := by
  rw [mem_SerS]; intro e
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

theorem serS_unit {S : Subring ℂ_[p]} {f : PowerSeries ℂ_[p]} (h : ∀ n, PowerSeries.coeff n f ∈ S) :
    (f : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := by
  rw [mem_SerS]; intro e
  have he : e = Finsupp.single () (e ()) := by ext; simp
  rw [he]; exact h (e ())

theorem serS_unit_iff {S : Subring ℂ_[p]} {f : PowerSeries ℂ_[p]} :
    (f : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit ↔ ∀ n, PowerSeries.coeff n f ∈ S := by
  refine ⟨fun h n => ?_, serS_unit⟩
  exact (mem_SerS S _).1 h (Finsupp.single () n)

theorem coeff_mul_second_variable (f : MvPowerSeries (Fin 2) ℂ_[p]) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (f * MvPowerSeries.X 1) =
      if 1 ≤ e 1 then MvPowerSeries.coeff (e - Finsupp.single 1 1) f else 0 := by
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, mul_one]
  congr 1
  simp [Finsupp.single_le_iff]

theorem single0_iff (e : Fin 2 →₀ ℕ) : e = Finsupp.single 0 (e 0) ↔ e 1 = 0 := by
  constructor
  · intro h; rw [h]; simp
  · intro h; ext j; fin_cases j <;> simp [h]

theorem fact_div {S : Subring ℂ_[p]} {H : MvPowerSeries (Fin 2) ℂ_[p]} {f : PowerSeries ℂ_[p]}
    (hf0 : PowerSeries.constantCoeff f = 0) (hfS : ∀ n, PowerSeries.coeff n f ∈ S) (hH : H ∈ SerS S (Fin 2))
    (hz : MvPowerSeries.subst ![MvPowerSeries.X 0,
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) f] H = 0) :
    ∃ Q ∈ SerS S (Fin 2),
      H = (MvPowerSeries.X 1 - PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) f) * Q := by
  set a : MvPowerSeries (Fin 2) ℂ_[p] := MvPowerSeries.X 0 with ha
  set b : MvPowerSeries (Fin 2) ℂ_[p] := MvPowerSeries.X 1 with hb
  set s : MvPowerSeries (Fin 2) ℂ_[p] := PowerSeries.subst a f with hs
  have ha0 : MvPowerSeries.constantCoeff a = 0 := MvPowerSeries.constantCoeff_X 0
  have hb0 : MvPowerSeries.constantCoeff b = 0 := MvPowerSeries.constantCoeff_X 1
  have hs0 : MvPowerSeries.constantCoeff s = 0 := PowerSeries.constantCoeff_subst_eq_zero ha0 f hf0
  have haS : a ∈ SerS S (Fin 2) := X_mem_SerS S 0
  have hbS : b ∈ SerS S (Fin 2) := X_mem_SerS S 1
  have hsS : s ∈ SerS S (Fin 2) := subst_mem_SerS S ha0 haS (serS_unit hfS)
  have hP : MvPowerSeries.HasSubst ![a, b + s] := hasSubst2 ha0 (by rw [map_add (f := _), hb0, hs0, add_zero])
  have hM : MvPowerSeries.HasSubst ![a, b - s] := hasSubst2 ha0 (by rw [map_sub, hb0, hs0, sub_zero])
  have hZ : MvPowerSeries.HasSubst ![a, (0 : MvPowerSeries (Fin 2) ℂ_[p])] := hasSubst2 ha0 (map_zero _)
  set Hp := MvPowerSeries.subst ![a, b + s] H with hHp

  have hback : MvPowerSeries.subst ![a, b - s] Hp = H := by
    rw [hHp, subst_pair_comp hM hP, subst_pair_first_variable hM, MvPowerSeries.subst_add hM, subst_pair_second_variable hM, hs, subst_pair_first_series hM, ← hs,
      sub_add_cancel, ha, hb, subst_pair_variables_self]

  have hzero : MvPowerSeries.subst ![a, (0 : MvPowerSeries (Fin 2) ℂ_[p])] Hp = 0 := by
    rw [hHp, subst_pair_comp hZ hP, subst_pair_first_variable hZ, MvPowerSeries.subst_add hZ, subst_pair_second_variable hZ, hs, subst_pair_first_series hZ, ← hs,
      zero_add]
    exact hz

  set Qt : MvPowerSeries (Fin 2) ℂ_[p] := fun e => MvPowerSeries.coeff (e + Finsupp.single 1 1) Hp with hQt
  set r : PowerSeries ℂ_[p] := PowerSeries.mk fun n => MvPowerSeries.coeff (Finsupp.single 0 n) Hp with hr
  have hdec : Hp = Qt * b + PowerSeries.subst a r := by
    ext e
    rw [map_add (f := _), hb, coeff_mul_second_variable, ha, PowerSeries.coeff_subst_single]
    by_cases he : e 1 = 0
    · have he' : e = Finsupp.single 0 (e 0) := (single0_iff e).2 he
      rw [if_neg (by omega), if_pos he', zero_add, hr, PowerSeries.coeff_mk, ← he']
    · have he' : ¬ e = Finsupp.single 0 (e 0) := fun h => he ((single0_iff e).1 h)
      rw [if_pos (by omega), if_neg he', add_zero]
      show MvPowerSeries.coeff e Hp = MvPowerSeries.coeff (e - Finsupp.single 1 1 + Finsupp.single 1 1) Hp
      rw [tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (by omega))]
  have hR : PowerSeries.subst a r = 0 := by
    have h1 := hzero
    rw [hdec, MvPowerSeries.subst_add hZ, MvPowerSeries.subst_mul hZ, subst_pair_second_variable hZ, mul_zero, zero_add, ha,
      subst_pair_first_series hZ] at h1
    exact h1
  have hdec' : Hp = Qt * b := by rw [hdec, hR, add_zero]
  have hQtS : Qt ∈ SerS S (Fin 2) := by
    have hHpS : Hp ∈ SerS S (Fin 2) :=
      mvsubst_mem_SerS S (Fin.forall_fin_two.2 ⟨by simpa using ha0, by simp [hb0, hs0]⟩)
        (Fin.forall_fin_two.2 ⟨by simpa using haS, by simpa using add_mem hbS hsS⟩) hH
    rw [mem_SerS]; intro e
    exact (mem_SerS S Hp).1 hHpS _
  refine ⟨MvPowerSeries.subst ![a, b - s] Qt, ?_, ?_⟩
  · exact mvsubst_mem_SerS S (Fin.forall_fin_two.2 ⟨by simpa using ha0, by simp [hb0, hs0]⟩)
      (Fin.forall_fin_two.2 ⟨by simpa using haS, by simpa using sub_mem hbS hsS⟩) hQtS
  · conv_lhs => rw [← hback, hdec', MvPowerSeries.subst_mul hM, hb, subst_pair_second_variable hM]
    ring

end PI.FglChordFactor.Wk
