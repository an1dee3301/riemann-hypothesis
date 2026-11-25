module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittFrameReduceRank
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelPar
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_frame_reduce_rank : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∃ (n' : ℕ) (J' : Matrix (Fin n') (Fin n') E) (X' Y' : Matrix (Fin n') (Fin r) E) (ι : GAd σ J' →* GAd σ J), IsHermND σ J' ∧ IsWittFrame σ J' X' Y' ∧ Continuous ι ∧ (∀ γ ∈ ratPts σ J', ι γ ∈ ratPts σ J) ∧ (∀ g', Sends σ J (ι g') (Xᵀ 0) (Xᵀ 0)) ∧ (∀ q ∈ minParOne σ J' X', ι q ∈ minParOne σ J X) ∧ ∀ a, IsTorus σ J X Y a → (∀ a', IsTorus σ J' X' Y' a' → ∀ s', ι (a' s') = a (Fin.cons 0 s')) ∧ (∀ (s₁ : ℝ) g', Commute (a (Fin.cons s₁ 0)) (ι g')) ∧ ∀ p ∈ minPar σ J X, ∃ g', ∃ q₀ ∈ minParOne σ J X, ∃ s₁ : ℝ, p = q₀ * a (Fin.cons s₁ 0) * ι g' ∧ ∀ h', (ι h')⁻¹ * q₀ * ι h' ∈ minParOne σ J X := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Levi.exists_levi | exact GlobalTheory.CompanionTheory.RedCov.Levi.exists_levi | (intros; apply GlobalTheory.CompanionTheory.RedCov.Levi.exists_levi <;> assumption)
