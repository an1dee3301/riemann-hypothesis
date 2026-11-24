module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAniso
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBottomTriIs
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialNormalizingFactorProductAnalyticNeZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.BottomIPData

theorem dSfun_bottom_ne_zero : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, GlobalTheory.LFun.dSfun D.host.E ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) ≠ 0 := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X h t
  apply GlobalTheory.LFun.dSfun_ne_zero_of_re_pos
  have h2 := (GlobalTheory.FunObj.SqNum.Model.bot_ranks (D := D) i j).1
  have hp : (0 : ℝ) < A'.rank := by rw [h.rank']; exact_mod_cast (by omega : 0 < SqNum.botSmall D i j)
  rw [show ((A'.rank : ℂ) / 2) = (((A'.rank : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  positivity

end GlobalTheory.BottomIPData
