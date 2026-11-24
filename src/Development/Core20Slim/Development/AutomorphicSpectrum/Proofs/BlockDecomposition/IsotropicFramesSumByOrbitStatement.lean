module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicFramesSumByOrbit
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActWOneApply
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Order.Real

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_frames_sum_by_orbit : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (rr : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → UJ (σ : E →+* E) (hypOne J)), (∀ q, gact σ (rr q) q.1 = e0 E M) → ∀ f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞, ∑' X : framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E), f X.1 = ∑' q : framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E), ∑' X : framesOne σ J n, f (gact σ (rr q)⁻¹ X.1) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.tsum_framesOne | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.tsum_framesOne | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.tsum_framesOne <;> assumption)
