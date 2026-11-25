module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefProd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowGrpEq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePointsRowPeriodConjLevelFubiniStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCosetProjectionVolumeConstMulStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHaarVolumeOfConjugateLatticeStatement
public import Batteries.Classes.RatCast
public import Batteries.Logic
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IterationAndLinearityCuspidal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.List.Nat.Range
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CellMass


set_option maxHeartbeats 1600000 in
theorem cell_mass : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ)
    (ρ : ∀ j, Measure ((rowGrp ch.G j).subgroupOf (GfC _))) (μ : ∀ j, Measure (GfC (ch.G.V (.grid D.R.m j)))),
    (∀ j ∈ idx D, (ρ j).IsHaarMeasure ∧ (μ j).IsHaarMeasure) → ∀ j ∈ idx D, ∃ c : ℂ, ∀ t Φ β b, IsRep t ch.S.B s β b →
      ∀ M M' : Vol ch.G, M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' → ∀ x : ℝ≥0, M.ν (.top j) = x • M'.ν (.top j) →
        ∀ hb : b j ∈ GfC _, cellWt (ρ j) (μ j) ((latGrp ch.G j).subgroupOf _) ⟨b j, hb⟩ * ((x : ℝ) : ℂ) =
          c * (GlobalTheory.RowWt.colCoef ch t β j : ℂ) := by
  refine GlobalTheory.RowReal.big_mono ?_ (Big.and GlobalTheory.T.finitePoints_rowPeriod_conjLevel_fubini (Big.and GlobalTheory.T.doubleCosetProjection_volume_const_mul GlobalTheory.T.exists_haar_volume_of_conjugate_lattice))
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch h s ρ μ hH j hj
  obtain ⟨hA, hB, hC⟩ := h
  obtain ⟨κ, la, ν, hκ, hla, hν, hAeq⟩ := hA j hj (ρ j) (hH j hj).1
  obtain ⟨κ', hκ', hBeq⟩ := hB s j hj ν hν
  obtain ⟨V₀, hV₀, hCeq⟩ := hC s j hj la hla
  have hjm : j ≤ D.R.m := by rw [idx, List.mem_range'_1] at hj; omega
  refine ⟨(((μ j).real (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup _) : Set (GfC _)) / (κ * κ' * V₀) : ℝ) : ℂ),
    fun t Φ β b hb M M' hM hM' x hx hbj => ?_⟩
  have e1 := hAeq ⟨b j, hbj⟩
  have e2 := hBeq t Φ β b hb M M' hM hM' x hx hbj
  have e3 := hCeq t β b hb hbj
  have hx0 : (x : ℝ) ≠ 0 := by
    intro h0
    have hH' := (hM.vtx (.top j) hjm).haar_fund.1
    have hz : M.ν (.top j) = 0 := by
      rw [hx, show x = 0 from NNReal.coe_eq_zero.1 h0, zero_smul]
    have hpos := Measure.IsOpenPosMeasure.open_pos (μ := M.ν (.top j)) Set.univ isOpen_univ Set.univ_nonempty
    rw [hz] at hpos
    exact hpos rfl
  set lv := la.real {n | (⟨b j, hbj⟩ : GfC _)⁻¹ * n.1 * ⟨b j, hbj⟩ ∈ (latGrp ch.G j).subgroupOf (GfC _)} with hlv
  set cc : ℝ := (GlobalTheory.RowWt.colCoef ch t β j : ℝ) with hcc
  have hlv0 : lv ≠ 0 := fun h0 => by rw [h0, zero_mul] at e3; exact hV₀.ne' e3.symm
  unfold cellWt
  rw [e1, e2]
  have key : (μ j).real (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup _) : Set (GfC _)) / (κ * lv * (κ' * x)) * x =
      (μ j).real (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup _) : Set (GfC _)) / (κ * κ' * V₀) * cc := by
    have hcc0 : cc ≠ 0 := fun h0 => by rw [h0, mul_zero] at e3; exact hV₀.ne' e3.symm
    have hk1 := hκ.ne'
    have hk2 := hκ'.ne'
    rw [← e3]
    field_simp
  have := congrArg (fun r : ℝ => (r : ℂ)) key
  simp only [hcc] at this
  push_cast at this ⊢
  exact this

end GlobalTheory.CellMass
