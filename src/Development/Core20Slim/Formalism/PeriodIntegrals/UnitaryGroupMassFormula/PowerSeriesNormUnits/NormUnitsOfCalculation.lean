module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.PhNormUnits
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.Development
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.ConstantCoeffFormalSMul
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.TendstoCoeffOfCont
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.ConstantCoeffVar
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.SimeqSubst1
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.StepUnitsOf
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.TraceAt
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.NormUnitsSubstitution
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Prod
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
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

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

theorem stepTrace_of (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense)
    (hZ : CalcZpScale) : StepTrace := by
  intro p _ l ex ph S hH hA δ hδ
  obtain ⟨hex0, hinv, hp2, h22, hswap, -, -, hintS, hIA, htr, -, -, hB, hunit⟩ := hH
  have hU2 := hunit ((2 : ℂ_[p]), (2 : ℂ_[p])) h22 (norm_two_of hp2) (norm_two_of hp2)
  have hph := ph_const_of hU2 hex0 hinv
  obtain ⟨t, ht⟩ := htr δ hδ
  have h2inv : ∃ h : ℤ_[p], 2 * zc h = 1 := by
    obtain ⟨h, hh⟩ := zc_inv_of (2 : ℤ_[p]) (by rw [zc_two]; exact norm_two_of hp2)
    exact ⟨h, by rwa [zc_two] at hh⟩
  exact trace_at hE hSub hC hD hZ hex0 hinv hph hIA hB δ.1 δ.2 (hintS δ hδ) (hintS δ.swap (hswap δ hδ)) t ht
    (hA δ hδ) hU2 h2inv (Xv ()) (constantCoeff_var ()) (int_X ())

theorem stepSum_of (hE : CalcEquiv) (hSub : CalcSubst) : StepSum := by
  intro p _ l ex ph S hH hA hT α hα
  obtain ⟨hex0, hinv, -, -, hswap, -, hmul, hintS, -, -, -, hdec, -, hunit⟩ := hH
  obtain ⟨β, hβ, γ, hγ, hb1, hb2, hg1, hg2, rfl⟩ := hdec α hα
  exact sum_at hE hSub hex0 hinv β γ (hintS γ hγ) (hA β hβ) (hT (β.swap * γ) (hmul β.swap (hswap β hβ) γ hγ))
    (hunit β hβ hb1 hb2) (hunit γ hγ hg1 hg2)

theorem target_of_calc (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense)
    (hZ : CalcZpScale) : Target :=
  target_of_steps (stepUnits_of hE hSub hC hD) (stepAll_of hE hSub) (stepTrace_of hE hSub hC hD hZ)
    (stepSum_of hE hSub)

theorem norm_units_of_calculation : Target :=
  target_of_calc norm_units_equivalence norm_units_substitution norm_units_closed_form natCast_dense_p_adic norm_units_zp_scaling

end PI.PhNormUnits.UnitaryGroupMassFormula
