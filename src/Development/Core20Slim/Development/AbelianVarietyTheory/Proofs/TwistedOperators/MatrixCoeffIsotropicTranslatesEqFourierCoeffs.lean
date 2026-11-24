module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicDualMiddlePartsSymplecticOrthogonal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedHeisenbergTermsPermutedRationalUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
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
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Bounded
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
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Bases
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistCoefUnfold

theorem pcoef : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ κ : ℝ, (∀ H : WO V W → ℂ, Continuous H → (∃ b : ℝ, ∀ w, ‖H w‖ ≤ b) → (∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w) → ∫ w in 𝓕V, H w ∂μV = κ • ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕', H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ) → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ (y : Mx D W.rank r) (a : Matrix (Fin W.rank) (Fin r) D.host.E), (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV) = ∫ t in 𝓨, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * (κ • (∫ y' in 𝓨, ∫ x in 𝓕', (heisO ψ V W (isoPart V W C y) F) (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ)) ∂μ := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ μV 𝓕V hμV h𝓕V μ' 𝓕' hμ' h𝓕' κ hκ F G hF hG y a
  have hth := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W
  have horth := GlobalTheory.TwistFormsOrth.orthogonal D V V' W r C B hs C' h1 h2 h3
  have hPt : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C y) F) := hth.1 _ F hF
  have hγrat : isoPart V W C (a.map (incA D)) ∈ ratL W V := by
    rw [← GlobalTheory.TwistEquiRat.ratW_eq_isoPart]; exact ⟨_, rfl⟩
  have hfirst : heisO ψ V W (isoPart V W C (y + a.map (incA D))) F =
      heisO ψ V W (isoPart V W C (a.map (incA D))) (heisO ψ V W (isoPart V W C y) F) := by
    rw [hth.2.1, GlobalTheory.TwistEquiRat.symplOH_isoPart V W C hs.frame, AddChar.map_zero_eq_one, one_smul,
      GlobalTheory.TwistEquiRat.isoPart_add, add_comm]
  have hpt : ∀ w, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) =
      ψ (symplO V W w (isoPart V W C (a.map (incA D)))) * (heisO ψ V W (isoPart V W C y) F w * star (G w)) := by
    intro w
    rw [hfirst, GlobalTheory.ThetaSchur.heisO_rat hPt hγrat]
    ring
  have hsym : ∀ t y' x, symplO V W (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)
      (isoPart V W C (a.map (incA D))) = symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))) := by
    intro t y' x
    rw [GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_left, horth.1 y' _,
      GlobalTheory.PlaceModel.symplO_skew V W (isoPart V W C (a.map (incA D))) (midPart V V' W B x), horth.2.1 _ x]
    simp
  have hHt : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C (y + a.map (incA D))) F) := hth.1 _ F hF
  have hHc : Continuous fun w => heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) :=
    hHt.cont.mul hG.cont.star
  have hHb : ∃ b : ℝ, ∀ w, ‖heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w)‖ ≤ b := by
    obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
    obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn hHc.continuousOn
    refine ⟨b, fun w => ?_⟩
    obtain ⟨g, hg, h⟩ := hKc w
    rw [← GlobalTheory.ThetaSchur.prod_periodic hψ hHt hG hg w]
    exact hb _ h
  have key := hκ _ hHc hHb (fun g hg w => GlobalTheory.ThetaSchur.prod_periodic hψ hHt hG hg w)
  rw [key]
  simp_rw [hpt, hsym, integral_const_mul]
  rw [← integral_smul]
  congr 1
  funext t
  rw [mul_smul_comm]

end GlobalTheory.TwistCoefUnfold
