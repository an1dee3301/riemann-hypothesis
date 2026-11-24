module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Nat.Gcd
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowVal

theorem givenLevel_inner {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E) :
    ∀ p : ℕ × ℕ, 1 ≤ p.1 → 1 ≤ p.2 → givenLevel G t w p = KO (Kw w) _ := by
  rintro ⟨_ | a, _ | b⟩ h1 h2
  · simp at h1
  · simp at h1
  · simp at h2
  · rfl

theorem oneAt : Big fun ch => OneAt ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t Φ β hβ w hw0 i
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hT := isTensor_Tflip hL ch.W ch.S.B t Φ hde hc w.2
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hcond : HasConductor (psiAt ch.W w.1) 1 :=
    (((Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w.1 w.2).square 0 hm 0 hm).cond
  have hce : depthAt ch.G w.1 = cosExp ch.G w.1 := by
    have e : 1 ≤ cosExp ch.G w.1 := by
      classical
      unfold cosExp
      rw [if_pos hw0]
      exact ch.G.pl.depth_pos _ _
    rw [depthAt, max_eq_left e]
  rw [hce] at hT
  haveI := (isUnitVol_unitVol w.1).1
  have hJ : ∀ j, 0 < j → j < (locGrid ch.G t w.1).m →
      givenLevel ch.G t w.1 ((locGrid ch.G t w.1).m, j) = KO (Kw w.1) _ := fun j hj hj' =>
    givenLevel_inner ch.G t w.1 _ (by change 1 ≤ D.R.m; omega) hj
  have key := OneCosetProof.oneCoset_of_isTensor (ν := unitVol w.1) one_le_sLen hcond hT hJ
  have hk : keepAt ch.G w.1 = false := by
    classical
    unfold keepAt
    simp [hw0]
  have hβw := hβ w
  rw [hk] at hβw
  exact key (β w) hβw i

end GlobalTheory.RowVal
