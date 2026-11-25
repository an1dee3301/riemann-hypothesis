module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdSinhcRootValueOfMatrixUnitP
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_sinhc_rootValueOfMatrixUnitP : ∀ (p q : ℕ) (h : ℕ → ℝ), ∏ ab : PIx p q, shc (rootP h ab.1) = (∏ i ∈ Finset.range (min p q), shc (2 * h i) * shc (h i) ^ (2 * (max p q - min p q))) * ∏ i ∈ Finset.range (min p q), ∏ j ∈ Finset.range (min p q), if i < j then (shc (h i - h j) * shc (h i + h j)) ^ 2 else 1 := by
  first | exact @GlobalTheory.PolarU.RootProd.prod_shc_rootP | exact GlobalTheory.PolarU.RootProd.prod_shc_rootP | (intros; apply GlobalTheory.PolarU.RootProd.prod_shc_rootP <;> assumption)
