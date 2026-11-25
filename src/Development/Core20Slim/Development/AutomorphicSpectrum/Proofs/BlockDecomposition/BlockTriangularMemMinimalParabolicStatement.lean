module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriangularMemMinimalParabolic
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_triangular_mem_minimal_parabolic : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (A : Type) [CommRing A] [Algebra F A] [TopologicalSpace A] (p : HA A σ J) (B : Matrix (Fin r) (Fin r) (A ⊗[F] E)), B.BlockTriangular id → (matHom A σ J p).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B → ∃ m : HA A σ J, (matHom A σ J m).1 = leviMat σ J A X Y (matHom A σ J p).1 ∧ (∃ d : Fin r → A ⊗[F] E, (matHom A σ J m).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * diagonal d) ∧ (∃ d' : Fin r → A ⊗[F] E, (matHom A σ J m).1 * Y.map (inclR (F := F) A) = Y.map (inclR (F := F) A) * diagonal d') ∧ (∃ B' : Matrix (Fin r) (Fin r) (A ⊗[F] E), B'.BlockTriangular id ∧ (∀ i, B' i i = 1) ∧ (matHom A σ J (m⁻¹ * p)).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B') ∧ ∀ z : Fin n → A ⊗[F] E, ((cT (σ : E →+* E) X * J).map (inclR (F := F) A)) *ᵥ z = 0 → ∃ a : Fin r → A ⊗[F] E, ((matHom A σ J (m⁻¹ * p)).1 - 1) *ᵥ z = X.map (inclR (F := F) A) *ᵥ a := by
  first | exact @GlobalTheory.CompanionTheory.KFin.LeviPt.exists_levi | exact GlobalTheory.CompanionTheory.KFin.LeviPt.exists_levi | (intros; apply GlobalTheory.CompanionTheory.KFin.LeviPt.exists_levi <;> assumption)
