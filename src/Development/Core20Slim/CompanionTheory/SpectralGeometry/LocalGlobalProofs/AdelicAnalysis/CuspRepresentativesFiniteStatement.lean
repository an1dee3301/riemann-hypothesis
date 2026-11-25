module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CuspRepresentativesFinite
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Batteries.Classes.RatCast
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Norm.Defs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_representatives_finite : ∀ (F : Type) [Field F] [NumberField F], ∃ (s : Finset SL(2, F)) (C : ℝ), ∀ c d : 𝓞 F, (c ≠ 0 ∨ d ≠ 0) → ∃ l : F, l ≠ 0 ∧ |((Algebra.norm ℚ l : ℚ) : ℝ)| ≤ C ∧ ∀ u : (𝓞 F)ˣ, ∃ r ∈ s, ∃ k : SL(2, F), (∀ i j, ∃ z : 𝓞 F, (z : F) = k i j) ∧ (r * k) 1 0 = ((u : 𝓞 F) : F) * l * (c : F) ∧ (r * k) 1 1 = ((u : 𝓞 F) : F) * l * (d : F) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.exists_finset_row_completion | exact GlobalTheory.CompanionTheory.SW.Core.exists_finset_row_completion | (intros; apply GlobalTheory.CompanionTheory.SW.Core.exists_finset_row_completion <;> assumption)
