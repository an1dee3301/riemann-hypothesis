module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotHasParamOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseChangeThetaLiftSatakeParameterEqAddSegment
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSumAuxiliaryPlaces
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalThetaInertPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.DivMod.Bootstrap
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Data.Multiset.Replicate
public import Mathlib.Data.Multiset.ZeroCons
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace GlobalTheory.Core.Rk.Exh.Model

open scoped ComplexConjugate Matrix NNReal ComplexOrder Kronecker
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}




theorem bcParam_rho {q : ℕ} (hq : q ≠ 0) (n : ℕ) : GlobalTheory.LGrp.bcParam n (LFun.Model.rhoU hq n) =
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str (Units.mk0 (q : ℂ) (by exact_mod_cast hq)) n := by
  have h := GlobalTheory.SphTheta.bcParam_map_mul 1 n (LFun.Model.rhoU hq n)
  simp only [one_mul, Multiset.map_id', LFun.Model.rhoU, ← zpow_neg] at h
  rw [h, Fin.sum_univ_eq_sum_range (fun k : ℕ => ({Units.mk0 (q : ℂ) (by exact_mod_cast hq) ^ ((n : ℤ) - 1 - 2 * (k : ℤ)),
    Units.mk0 (q : ℂ) (by exact_mod_cast hq) ^ (-((n : ℤ) - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ)) (n / 2)]
  rcases Nat.even_or_odd' n with ⟨d, rfl | rfl⟩
  · rw [GlobalTheory.SphTheta.str_even _ d _ (by push_cast; rfl), show 2 * d / 2 = d by omega, show 2 * d % 2 = 0 by omega]
    simp
  · rw [GlobalTheory.SphTheta.str_odd _ d _ (by push_cast; rfl), show (2 * d + 1) / 2 = d by omega, show (2 * d + 1) % 2 = 1 by omega]
    simp

theorem seg_eq_str {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} (hq : q ≠ 0)
    (h : Ideal.absNorm w.asIdeal = q ^ 2) (n : ℕ) :
    LFun.seg w 1 n = GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str (Units.mk0 (q : ℂ) (by exact_mod_cast hq)) n := by
  have hu : ∀ f : ℕ → ℂˣ, (Finset.range n).val.map f = ∑ i ∈ Finset.range n, ({f i} : Multiset ℂˣ) := fun f => by
    rw [Finset.sum_eq_multiset_sum, ← Multiset.sum_map_singleton ((Finset.range n).val.map f), Multiset.map_map]; rfl
  rw [GlobalTheory.SphTheta.str_eq_sum, Int.toNat_natCast, LFun.seg, hu, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj := Finset.mem_range.1 hj
  congr 1
  refine Units.ext ?_
  rw [one_mul, LFun.coe_npowU, LFun.npow, h, Units.val_zpow_eq_zpow_val, Units.val_mk0, Nat.cast_sub (by omega),
    Nat.cast_sub (by omega), Nat.cast_pow, ← Complex.cpow_intCast, ← Complex.natCast_cpow_natCast_mul]
  congr 1
  push_cast
  ring


end GlobalTheory.Core.Rk.Exh.Model

end
