module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianUnitFormDiagonalizes
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs

@[expose] public section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_unit_form_diagonalizes : ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A), (∀ y, σ (σ y) = y) → (∀ (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det → ∃ x, IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hform σ J x x)) → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det → ∃ (g : Matrix (Fin m) (Fin m) A) (d : Fin m → A), IsUnit g.det ∧ (∀ i, IsUnit (d i) ∧ σ (d i) = d i) ∧ HeckeCharacterZeroLocus.SiegelWeilU.cT σ g * J * g = Matrix.diagonal d := by
  first | exact @GlobalTheory.CompanionTheory.SW.RingDiag.diagonalise | exact GlobalTheory.CompanionTheory.SW.RingDiag.diagonalise | (intros; apply GlobalTheory.CompanionTheory.SW.RingDiag.diagonalise <;> assumption)
