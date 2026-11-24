module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSignatureOfGramEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Init.Classical
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
public import Init.Omega.Logic
public import Init.Prelude
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotRankSize

theorem bot_arith (D : D7) (i j : ℕ) :
    Even (SqNum.botBig D i j + SqNum.botSmall D i j) ∧ SqNum.botSmall D i j + 2 < SqNum.botBig D i j ∧
      1 < SqNum.botSmall D i j := by
  have hk := D.R.k_even
  have hm := D.R.m_even
  have ht := D.R.t_odd
  have h3 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  rw [Nat.even_iff] at hk hm
  rw [Nat.odd_iff] at ht
  simp only [SqNum.botBig, SqNum.botSmall, rankV, sLen, Formalism.BasicNotions.Ranks.r]
  have e1 : (j + 1) * D.R.t = j * D.R.t + D.R.t := by ring
  have e2 : (i + 1) * (D.R.k + D.R.m - 1 + 6) = i * (D.R.k + D.R.m - 1 + 6) + (D.R.k + D.R.m - 1 + 6) := by ring
  rw [e1, e2]
  generalize j * D.R.t = A
  generalize i * (D.R.k + D.R.m - 1 + 6) = B
  rw [Nat.even_iff]
  omega

theorem bottom_ranks : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ i j : Fin D.R.m, Even (SqNum.botBig D i j + SqNum.botSmall D i j) ∧ SqNum.botSmall D i j + 2 < SqNum.botBig D i j ∧ 1 < SqNum.botSmall D i j := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro i j
  exact bot_arith D i j

end GlobalTheory.BotRankSize

end
