module

public import Mathlib
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.RderCAdjoint

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem Rder_neg_dir (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    Rder θ V τ (-X) φ = -Rder θ V τ X φ := by
  funext g
  have := deriv_comp_neg (fun t : ℝ => φ (g * oneP θ V τ X t)) 0
  simpa only [Rder, oneP, smul_neg, neg_smul, neg_zero, Pi.neg_apply] using this

theorem conjAt_adjoint (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    conjAt V τ ((gramAt D V τ)⁻¹ * Zᴴ * gramAt D V τ) = -Z := by
  have hu := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have hH := GlobalTheory.SmoothAutCheck.gramAt_herm V τ
  unfold conjAt
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hH,
    ← mul_assoc, nonsing_inv_mul _ hu, one_mul, mul_assoc, nonsing_inv_mul _ hu, mul_one]

theorem RderC_adjoint_eq (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    RderC θ V τ ((gramAt D V τ)⁻¹ * Zᴴ * gramAt D V τ) φ =
      -Rder θ V τ ((1 / 2 : ℂ) • (Z + conjAt V τ Z)) φ +
        Complex.I • Rder θ V τ ((1 / (2 * Complex.I)) • (Z - conjAt V τ Z)) φ := by
  unfold RderC
  rw [conjAt_adjoint]
  have hW : (gramAt D V τ)⁻¹ * Zᴴ * gramAt D V τ = -conjAt V τ Z := by simp [conjAt]
  rw [hW, ← Rder_neg_dir, ← smul_neg, neg_add, add_comm (-Z), neg_sub_neg]

theorem rderC_adjoint : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
    (A : Submodule ℂ (GA D V → ℂ)) (b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ),
    (∀ X ∈ lieAt V τ, ∀ x ∈ A, ∀ y ∈ A, b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    ∀ (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ), ∀ x ∈ A, ∀ y ∈ A,
      b x (RderC θ V τ Z y) = b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y := by
  intro D θ V τ A b hb Z x hx y hy
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  rw [RderC_adjoint_eq]
  unfold RderC
  rw [map_add (f := _), map_smul, hb _ h1 x hx y hy, hb _ h2 x hx y hy, map_add (f := _), map_neg, map_smulₛₗ]
  simp

end GlobalTheory.RderCAdjoint

end
