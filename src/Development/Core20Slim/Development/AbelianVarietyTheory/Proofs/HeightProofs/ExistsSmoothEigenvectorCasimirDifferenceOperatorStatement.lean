module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSmoothEigenvectorCasimirDifferenceOperator
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.InnerDRepSq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Formalism.RealPlaceAnalysis.Complexify
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_eigenvector_casimirDifferenceOperator : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)) (d e : ℕ) (X : Fin d → Mx n) (Y : Fin e → Mx n), Std ε σ → (∀ i, X i ∈ lieSet ε) → (∀ b, Y b ∈ lieSet ε) → (∀ k ∈ Kset ε, ∀ v, Sm ε σ v → casOp σ X Y (σ k v) = σ k (casOp σ X Y v)) → ∃ (u : H) (χ : ℂ), Sm ε σ u ∧ u ≠ 0 ∧ casOp σ X Y u = χ • u := by
  first | exact @GlobalTheory.TypeSum.CasBasis.exists_eigen_casOp | exact GlobalTheory.TypeSum.CasBasis.exists_eigen_casOp | (intros; apply GlobalTheory.TypeSum.CasBasis.exists_eigen_casOp <;> assumption)
