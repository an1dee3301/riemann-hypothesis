module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicMeanChangesByScalarOfTrivialActionStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjEqZeroOfSymplO
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipMean

theorem heisO_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (f : WO V W → ℂ) : heisO ψ V W 0 f = f := by
  funext x
  unfold heisO symplOH symplO hO
  simp

theorem symplO_zero_left {D : D7} (V W : HSp D) (z : WO V W) : symplO V W 0 z = 0 := by
  unfold symplO hO
  simp

theorem mean_target : ∀ (D : D7) (V W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D s V.rank)) (𝓐 : Set (Mx D s V.rank)), IsCovolOne (ratMx D s V.rank) μ 𝓐 → ∀ (n : NI W L) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∫ a in 𝓐, ω (1, (n : GA D W)) f (HMul.hMul (L.map (incA D)) (a : Matrix (Fin s) (Fin V.rank) (AE D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ = ∫ a in 𝓐, f (HMul.hMul (L.map (incA D)) (a : Matrix (Fin s) (Fin V.rank) (AE D)) : Matrix (Fin W.rank) (Fin V.rank) (AE D)) ∂μ := by
  intro D V W s L hL ψ χS χT ω hω μ 𝓐 hcov n f hf
  have hiso := iso_rat hL
  have e1 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hm1 : Formalism.L2.Theta.mt V 1 = 1 := by
    unfold Formalism.L2.Theta.mt
    simp
  have hact : ∀ (g : GA D W) (x : WO V W), actO V W 1 g x = HMul.hMul (Formalism.L2.Theta.mt W g) x := by
    intro g x
    unfold actO
    rw [inv_one, hm1, Matrix.mul_one]
  have hrk : L.rank = s := by
    rw [Matrix.rank_eq_finrank_span_cols]
    exact (finrank_span_eq_card hL.2.1).trans (Fintype.card_fin s)
  have hsym : ∀ y y' : Mx D s V.rank, symplO V W (HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D))) (HMul.hMul (HMul.hMul (L.map (incA D)) y') ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D))) = 0 := by
    intro y y'
    rw [e1, Matrix.mul_one, Matrix.mul_one]
    exact symplO_frame hiso y y'
  have hsc : ∀ g : GA D W,
      (∀ y : Mx D s V.rank, HMul.hMul (mt W g) (HMul.hMul (GlobalTheory.MixModel.rat L) y) = HMul.hMul (GlobalTheory.MixModel.rat L) y) →
      (∀ x : WO V W, HMul.hMul (GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat L)) (HMul.hMul (GlobalTheory.MixModel.gA W) x) = 0 →
        ∃ y : Mx D s V.rank, HMul.hMul (mt W g) x = x + HMul.hMul (GlobalTheory.MixModel.rat L) y) →
      ∃ c : ℂ, c ≠ 0 ∧ Sc ψ ω (GlobalTheory.MixModel.rat L) μ 𝓐 g c := by
    intro g hg1 hg2
    have hfix : ∀ y : Mx D s V.rank, actO V W 1 g (HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D))) = HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D)) := by
      intro y
      rw [e1, Matrix.mul_one, hact]
      exact hg1 y
    have hmov : ∀ x : WO V W, (∀ y : Mx D s V.rank, symplO V W x (HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D))) = 0) → ∃ y : Mx D s V.rank, actO V W 1 g x = x + HMul.hMul (HMul.hMul (L.map (incA D)) y) ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D)) := by
      intro x hx
      rw [e1] at hx
      simp only [Matrix.mul_one] at hx
      obtain ⟨y, hy⟩ := hg2 x (adj_eq_zero_of_symplO (C := GlobalTheory.MixModel.rat L) hx)
      refine ⟨y, ?_⟩
      rw [e1, Matrix.mul_one, hact]
      exact hy
    obtain ⟨c, hc⟩ := GlobalTheory.T.isotropicMean_changes_by_scalar_of_trivial_action D V W s V.rank L 1 hrk (Matrix.rank_one.trans (Fintype.card_fin _)) hsym ψ χS χT ω hω μ 𝓐 hcov 1 g hfix hmov
    refine ⟨c, Circle.coe_ne_zero c, ?_⟩
    intro f' hf'
    have h0 := hc f' hf' 0 (fun y => symplO_zero_left V W _)
    simp only [heisO_zero, e1, Matrix.mul_one] at h0
    exact h0
  have key := mean_unip hL hω hcov hsc n.2 f hf
  unfold meanL at key
  rw [one_mul] at key
  exact key

end GlobalTheory.UnipMean

end
