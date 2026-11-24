module

public import Mathlib
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupTriangles.LogThirdPointSum
public import Development.Core20Slim.Formalism.PeriodIntegrals.FglTriFactor
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.CoeffPowMemS
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GlueHoldsVar
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.SubstMem
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupTriangles.CoeffSubstUpdZero
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupTriangles.LiftedThirdRootSubXZeroNeZero
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupTriangles.PairSubstXZero
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupTriangles.SubstUpdateVarTwoLiftedThirdRoot
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace PI.FglTriFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)

variable {p : ℕ} [Fact p.Prime]

theorem cc_pr_eq {x y : MvPowerSeries (Fin 3) ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) (f : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.constantCoeff (pr x y f) = MvPowerSeries.constantCoeff f := by
  unfold pr
  have hz : ∀ i, MvPowerSeries.constantCoeff (![x, y] i) = 0 := fun i => by fin_cases i <;> simpa
  have ha : MvPowerSeries.HasSubst ![x, y] := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hz
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by rw [hz i]; exact IsNilpotent.zero)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hz
  rw [MvPowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hd
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hs
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)]
    · simp
    · rw [map_pow]
      fin_cases s <;> simp [hx, hy] <;> exact hs

theorem main : Lemma := by
  intro p _ W wq ex h1 h2 h3 h4 h6 _ hW hex0 hex hadd
  obtain ⟨S, hS⟩ := PI.AddIntG.Wk.exists_intS p
  have hS1 : W.a₁ ∈ S := (hS _).2 h1
  have hS2 : W.a₂ ∈ S := (hS _).2 h2
  have hS3 : W.a₃ ∈ S := (hS _).2 h3
  have hS4 : W.a₄ ∈ S := (hS _).2 h4
  have hS6 : W.a₆ ∈ S := (hS _).2 h6
  have hint : ∀ {σ : Type} (F : MvPowerSeries σ ℂ_[p]), IntegralMv F ↔ F ∈ SerS S σ := fun F => by
    rw [mem_SerS]
    exact forall_congr' fun e => (hS _).symm
  have hF : add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∈ SerS S (Fin 2) := (hint _).1 hadd
  have hwq := PI.AddIntG.Wk.wq_mem hS1 hS2 hS3 hS4 hS6 hW
  obtain ⟨μ, hμS, hμ⟩ := mu_exists hwq
  obtain ⟨m, hmS, hm1, hmμ⟩ := m_exists hS1 hS2 hS3 hS4 hS6 hW hμS hμ
  obtain ⟨u1, hu1S, hu11, hu1⟩ := add_factor hS1 hS2 hS3 hS4 hS6 hW hex0 hex hF
  obtain ⟨u, huS, hu0, hu⟩ := sub_factor hS1 hS2 hS3 hS4 hS6 hW hex0 hex hF
  have hl0 := cc_flog W wq
  have hsub : ∀ i j : Fin 3, sub (flog W wq) ex (MvPowerSeries.X i) (MvPowerSeries.X j) =
      (MvPowerSeries.X i - MvPowerSeries.X j) * pr (MvPowerSeries.X i) (MvPowerSeries.X j) u := by
    intro i j
    have ha := hasSubst_pr (h0X (p := p) i) (h0X (p := p) j)
    rw [sub_pr hl0 (h0X i) (h0X j), hu]
    unfold pr
    rw [MvPowerSeries.subst_mul ha, MvPowerSeries.subst_sub ha, MvPowerSeries.subst_X ha,
      MvPowerSeries.subst_X ha]
    simp
  have hvS : ∀ i j : Fin 3, pr (MvPowerSeries.X i) (MvPowerSeries.X j) u ∈ SerS S (Fin 3) := fun i j =>
    pr_mem (h0X i) (h0X j) (X_mem_SerS' S i) (X_mem_SerS' S j) huS
  have hv1 : ∀ i j : Fin 3, MvPowerSeries.constantCoeff (pr (MvPowerSeries.X i) (MvPowerSeries.X j) u) = 1 :=
    fun i j => (cc_pr_eq (h0X i) (h0X j) u).trans hu0
  have hw1 : MvPowerSeries.constantCoeff (u1 * pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) u *
      pr (MvPowerSeries.X 1) (MvPowerSeries.X 2) u * pr (MvPowerSeries.X 2) (MvPowerSeries.X 0) u) = 1 := by
    rw [map_mul, map_mul, map_mul, hu11, hv1, hv1, hv1]
    norm_num
  have hwS : u1 * pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) u * pr (MvPowerSeries.X 1) (MvPowerSeries.X 2) u *
      pr (MvPowerSeries.X 2) (MvPowerSeries.X 0) u ∈ SerS S (Fin 3) :=
    mul_mem (mul_mem (mul_mem hu1S (hvS 0 1)) (hvS 1 2)) (hvS 2 0)
  have hinv := MvPowerSeries.mul_inv_cancel (u1 * pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) u *
      pr (MvPowerSeries.X 1) (MvPowerSeries.X 2) u * pr (MvPowerSeries.X 2) (MvPowerSeries.X 0) u)
    (by rw [hw1]; exact one_ne_zero)
  refine ⟨m * (u1 * pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) u *
      pr (MvPowerSeries.X 1) (MvPowerSeries.X 2) u * pr (MvPowerSeries.X 2) (MvPowerSeries.X 0) u)⁻¹,
    (hint _).2 (mul_mem hmS (PI.AddIntG.Wk.inv_mem_SerS S hw1 hwS)), ?_, ?_⟩
  · rw [map_mul, MvPowerSeries.constantCoeff_inv, hw1, hm1, inv_one, mul_one]
  · rw [T_eq, hμ, hmμ, hu1, hsub 0 1, hsub 1 2, hsub 2 0]
    linear_combination (-((MvPowerSeries.X 2 - s3 W wq) * (MvPowerSeries.X 0 - MvPowerSeries.X 1) *
      (MvPowerSeries.X 1 - MvPowerSeries.X 2) * (MvPowerSeries.X 2 - MvPowerSeries.X 0) * m)) * hinv

end PI.FglTriFactor.Wk
