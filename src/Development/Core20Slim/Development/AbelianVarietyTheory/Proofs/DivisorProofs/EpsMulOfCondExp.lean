module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Batteries.Logic
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.Lattice.Lemmas
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqStepArith

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt)

theorem chrW_chs {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (x : (Fv D.host.F v)ˣ) :
    chrW (GlobalTheory.SqStep.chs G i j t).ν τ x = (nuH G t i j).loc (GlobalTheory.AdelicU.splitPrime τ)
      (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom x) := by
  have e : (GlobalTheory.SqStep.chs G i j t).ν = G.nu t i (j + 1) := by
    show (Lc.mu t (j + 1) * Lc.eta ^ _) / (G.ch.chi _ * Lc.eta ^ _) = _
    rw [mul_div_mul_right_eq_div]
    rfl
  show GlobalTheory.LFun.locChar (GlobalTheory.SqStep.chs G i j t).ν _ _ = _
  rw [e, GlobalTheory.LFun.locChar_eq_of_chrEq (chrEq_nu G t i j hL)]

theorem eps_mul_of_condExp {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)}
    (ν₀ ξ : (Fv F v)ˣ →* ℂˣ) (s : (Fv F v)ˣ) (z : ℤ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (ν₀ * ξ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀) :
    (ν₀ s : ℂ) * eps ψ ν₀ z * gauss ψ (ν₀ * ξ) =
      (((ξ (s * unifAt v ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀))⁻¹ : ℂˣ) : ℂ) * gauss ψ ν₀ *
        (((ν₀ * ξ) s : ℂ) * eps ψ (ν₀ * ξ) z) := by
  unfold eps
  rw [h]
  simp only [MonoidHom.mul_apply, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, mul_inv, Units.val_inv_eq_inv_val]
  have h1 : (ξ s : ℂ) ≠ 0 := Units.ne_zero _
  have h2 : (ξ (unifAt v) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp
  ring

theorem chs_T_base {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (i j : Fin D.R.m) : (GlobalTheory.SqStep.chs G i j μ₀).T = G.pl.S0 := by
  classical
  have hQ : Lc.Q μ₀ = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
    have h := (hL.Q_ram μ₀ PP).2 (Or.inl hPP)
    apply h
    rw [hL.xi_base]
    intro x _
    rfl
  have htw : twPl G μ₀ = ∅ := by
    unfold twPl locPl
    rw [hQ, Finset.union_empty]
    exact Finset.filter_false_of_mem fun w hw h => h hw
  show G.pl.S0 ∪ (twPl G μ₀).image _ = _
  rw [htw, Finset.image_empty, Finset.union_empty]

end GlobalTheory.SqStepArith
