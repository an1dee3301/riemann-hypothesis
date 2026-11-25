module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelDomainOpenSubgroupBound
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_domain_open_subgroup_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Ω Cm : Set (GAd σ J)) (c : ℝ) (U : Subgroup (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → IsCompact Cm → 0 < c → IsOpen (U : Set (GAd σ J)) → ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ∀ s : Fin r, ∀ m ∈ unipRad σ J (pre X s), ∃ γ ∈ ratPts σ J, ∃ u κ : GAd σ J, CloseInf σ J u (M / ratio t s) ∧ κ ∈ U ∧ κ ∈ finPts σ J ∧ m * (p * a * k) = γ * (p * a * k) * u * κ := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.near_cusp | exact GlobalTheory.CompanionTheory.RapidDecay.near_cusp | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.near_cusp <;> assumption)
