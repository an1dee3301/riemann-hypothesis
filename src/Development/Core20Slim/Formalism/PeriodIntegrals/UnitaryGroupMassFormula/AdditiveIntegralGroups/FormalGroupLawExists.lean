module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.VarZeroSubVarOneNe
public import Development.Core20Slim.Formalism.PeriodIntegrals.AddIntG
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GuLine
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.SubstMem
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.ThirdRootSubVarZeroNeZero
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.LinearCombination.Lemmas
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

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

def bZ (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Fin 2 → MvPowerSeries (Fin 2) ℂ_[p] :=
  fun i => if i = 0 then 0 else Z3 W wq

theorem bZ_const (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    ∀ i, MvPowerSeries.constantCoeff (bZ W wq i) = 0 := by
  intro i
  unfold bZ
  split_ifs
  · exact map_zero _
  · exact constantCoeff_thirdRoot W wq

theorem hasSubst_bZ (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.HasSubst (bZ W wq) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (bZ_const W wq)

theorem Fch_eq (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    Fch W wq = MvPowerSeries.subst (bZ W wq) (Z3 W wq) := rfl

theorem subst_psubst {a : MvPowerSeries (Fin 2) ℂ_[p]} (ha : PowerSeries.HasSubst a)
    {b : Fin 2 → MvPowerSeries (Fin 2) ℂ_[p]} (hb : MvPowerSeries.HasSubst b) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst b (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst b a) f := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply ha.const hb]

theorem constantCoeff_flog' (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (flog W wq) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold PI.AddIntG.flog
  rw [PowerSeries.coeff_mk, if_pos rfl]

theorem constantCoeff_Fch (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (Fch W wq) = 0 := by
  rw [Fch_eq]
  exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_bZ W wq) (bZ_const W wq) (constantCoeff_thirdRoot W wq)

theorem Fch_mem {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq) :
    ∀ n, MvPowerSeries.coeff n (Fch W wq) ∈ S := by
  have hZ := thirdRoot_mem_coeffSubring h1 h2 h3 h4 h6 h
  have hb : ∀ i, bZ W wq i ∈ SerS S (Fin 2) := by
    intro i
    unfold bZ
    split_ifs
    · exact zero_mem _
    · exact hZ
  rw [Fch_eq]
  exact (mem_SerS S _).mp (mvsubst_mem_SerS S (bZ_const W wq) hb hZ)

theorem flog_Fch {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.subst (Fch W wq) (flog W wq) =
      PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) +
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) := by
  have hA := abel h
  have hb := hasSubst_bZ W wq
  have hX : ∀ i : Fin 2, PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have hZ : PowerSeries.HasSubst (Z3 W wq) := PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_thirdRoot W wq)
  have hB := congrArg (MvPowerSeries.substAlgHom (R := ℂ_[p]) hb) hA
  rw [map_add (f := _), map_add (f := _), map_zero, MvPowerSeries.coe_substAlgHom, subst_psubst (hX 0) hb,
    subst_psubst (hX 1) hb, subst_psubst hZ hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb,
    ← Fch_eq] at hB
  have h0 : bZ W wq 0 = 0 := by simp [bZ]
  have h1' : bZ W wq 1 = Z3 W wq := by simp [bZ]
  rw [h0, h1', PowerSeries.subst_zero_of_constantCoeff_zero (constantCoeff_flog' W wq)] at hB
  linear_combination hB - hA

theorem formalGroupLawExists : KeyF := by
  intro p _ S W wq h1 h2 h3 h4 h6 h
  exact ⟨Fch W wq, Fch_mem h1 h2 h3 h4 h6 h, constantCoeff_Fch W wq, flog_Fch h⟩

end PI.AddIntG.Wk
