module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsotropicDualFrameOfSplitEmbeddingStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalStabiliserScalesRestrictionStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalLeviScalingIsotropicFrameStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionInvariantRationalLeviScalingStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentLeviMatrixActionIdentityStatement
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipRes

theorem res_unip : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (n : NI V C) (f : WO V W → ℂ), IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω ((n : GA D V), 1) f) = res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ n f hf
  obtain ⟨C', h1, h2, h3⟩ := GlobalTheory.T.exists_isotropicDualFrame_of_splitEmbedding D V V' r C B hs
  obtain ⟨a, haQ, haC, haB, haC'⟩ := GlobalTheory.T.exists_rationalLevi_scaling_isotropicFrame D V V' r C C' B hs h1 h2 h3
  obtain ⟨l, hl⟩ := GlobalTheory.T.thetaRestriction_invariant_rationalLeviScaling D V V' W r C B hs a haQ haC haB ψ χS χT ω hω μ 𝓨 hμ
  have hp : ∀ p f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (ω p f) := hω.om_pres
  have hm : ∀ x y : GA D V, ∀ f, ω (x * y, 1) f = ω (x, 1) (ω (y, 1) f) := by
    intro x y f
    rw [show ((x * y, 1) : GA D V × GA D W) = (x, 1) * (y, 1) by simp, map_mul, Module.End.mul_apply]
  have key : ∀ g ∈ NI V C, ∀ f, IsThetaFunO ψ V W f →
      res V V' W C B μ 𝓨 (ω (g, 1) f) = res V V' W C B μ 𝓨 f := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hx1, hx2, hx3⟩ := hx
      obtain ⟨m, hmN, rfl⟩ := GlobalTheory.T.unipotent_levi_matrix_action_identity D V V' r C C' B hs h1 h2 h3 a haC haB haC' x hx1 hx2 hx3
      obtain ⟨c, hc⟩ := GlobalTheory.T.unipotentRadical_stabiliser_scales_restriction D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ m hmN
      intro f hf
      have e1 : res V V' W C B μ 𝓨 (ω (a, 1) (ω (a⁻¹, 1) (ω (m⁻¹, 1) f))) = res V V' W C B μ 𝓨 (ω (m⁻¹, 1) f) := by
        rw [← hm, mul_inv_cancel, show ((1 : GA D V), (1 : GA D W)) = 1 from rfl, map_one]; rfl
      have e2 : res V V' W C B μ 𝓨 (ω (m, 1) (ω (m⁻¹, 1) f)) = res V V' W C B μ 𝓨 f := by
        rw [← hm, mul_inv_cancel, show ((1 : GA D V), (1 : GA D W)) = 1 from rfl, map_one]; rfl
      rw [hm, hm, hm, hl _ (hp _ _ (hp _ _ (hp _ _ hf))), hc _ (hp _ _ (hp _ _ hf)), smul_smul, mul_comm,
        ← smul_smul, ← hl _ (hp _ _ (hp _ _ hf)), e1, ← hc _ (hp _ _ hf), e2]
    | one => intro f hf; rw [show ((1 : GA D V), (1 : GA D W)) = 1 from rfl, map_one]; rfl
    | mul x y _ _ hx hy => intro f hf; rw [hm, hx _ (hp _ _ hf), hy _ hf]
    | inv x _ hx =>
      intro f hf
      have := hx (ω (x⁻¹, 1) f) (hp _ _ hf)
      rw [← this, ← hm, mul_inv_cancel, show ((1 : GA D V), (1 : GA D W)) = 1 from rfl, map_one]; rfl
  exact key n n.2 f hf
end GlobalTheory.UnipRes
