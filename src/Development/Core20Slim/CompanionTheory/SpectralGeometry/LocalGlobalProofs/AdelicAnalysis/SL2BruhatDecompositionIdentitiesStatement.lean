module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SL2BruhatDecompositionIdentities
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.SL2_bruhat_decompositions_and_w_inv : ∀ (R : Type) [CommRing R] (g : SL(2, R)), (∀ c : Rˣ, g 1 0 = (c : R) → g = nMat (g 0 0 * ((c⁻¹ : Rˣ) : R)) * mMat (-c⁻¹) * wMat * nMat (g 1 1 * ((c⁻¹ : Rˣ) : R))) ∧ (∀ a : Rˣ, g 0 0 = (a : R) → g = wMat⁻¹ * nMat (-(g 1 0 * ((a⁻¹ : Rˣ) : R))) * wMat * mMat a * nMat (g 0 1 * ((a⁻¹ : Rˣ) : R))) ∧ (∀ a : Rˣ, g 0 0 = (a : R) → g 1 0 = 0 → g = nMat (g 0 1 * (a : R)) * mMat a) ∧ (wMat : SL(2, R))⁻¹ = wMat * wMat * wMat := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition.decompositions | exact GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition.decompositions | (intros; apply GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition.decompositions <;> assumption)
