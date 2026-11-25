module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterSizeConditionsNumericBounds
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HBdNonneg
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameterSizeConditions_numericBounds : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → (bigN D : ℝ) ≤ large₂.sc.b ∧ (D.R.f : ℝ) ≤ large₂.sc.b ∧ 1 ≤ bigN D ∧ 1 ≤ D.R.f ∧ 2 ≤ D.R.m ∧ 1 ≤ D.host.rdE ∧ Real.log D.host.rdE ≤ Real.log large₂.sc.b / 100 ∧ 12 ≤ large₂.sc.b := by
  first | exact @GlobalTheory.SizesOfRows.sizes_of_sizeRows | exact GlobalTheory.SizesOfRows.sizes_of_sizeRows | (intros; apply GlobalTheory.SizesOfRows.sizes_of_sizeRows <;> assumption)
