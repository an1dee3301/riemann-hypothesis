module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWittDecompositionIsotropicSplitUnipotentStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TowerSurj

open GlobalTheory.MixModel (rat sandwich HypDec)
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition (isoPart midPart res IsIsoSplit)

variable {D : D7}

section Emb

variable {V V' H Z : HSp D} {r : ℕ} (d : HypDec V V' r) (dH : HypDec H Z r)

def embMat : Matrix (Fin V.rank) (Fin H.rank) D.host.E := d.e * dH.qX + d.e' * dH.qY

theorem ee_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.eᴴ * (S.gram * d.e) = 0 := by
  rw [← Matrix.mul_assoc]
  exact d.ee

theorem e'e'_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.e'ᴴ * (S.gram * d.e') = 0 := by
  rw [← Matrix.mul_assoc]
  exact d.e'e'

theorem e'e_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.e'ᴴ * (S.gram * d.e) = 1 := by
  rw [← Matrix.mul_assoc]
  exact d.e'e

theorem ee'_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.eᴴ * (S.gram * d.e') = 1 := by
  have h := congrArg Matrix.conjTranspose d.e'e
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    GlobalTheory.MixModel.gram_conjTranspose, Matrix.conjTranspose_one] at h
  exact h

theorem ei₀_assoc {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.eᴴ * (S.gram * d.i₀) = 0 := by
  have h := congrArg Matrix.conjTranspose d.i₀e
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    GlobalTheory.MixModel.gram_conjTranspose, Matrix.conjTranspose_zero] at h
  exact h

theorem embMat_e : embMat d dH * dH.e = d.e := by
  have h1 := e'e_assoc dH
  have h0 := ee_assoc dH
  simp only [embMat, GlobalTheory.MixModel.HypDec.qX, GlobalTheory.MixModel.HypDec.qY, Matrix.add_mul, Matrix.mul_assoc, h1, h0,
    Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem embMat_e' : embMat d dH * dH.e' = d.e' := by
  have h1 := ee'_assoc dH
  have h0 := e'e'_assoc dH
  simp only [embMat, GlobalTheory.MixModel.HypDec.qX, GlobalTheory.MixModel.HypDec.qY, Matrix.add_mul, Matrix.mul_assoc, h1, h0,
    Matrix.mul_one, Matrix.mul_zero, zero_add]

theorem iso_embMat : d.eᴴ * V.gram * embMat d dH = dH.eᴴ * H.gram := by
  have h1 : d.eᴴ * V.gram * d.e' = 1 := by
    rw [Matrix.mul_assoc]
    exact ee'_assoc d
  rw [embMat, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.ee, h1, Matrix.zero_mul, Matrix.one_mul,
    zero_add]
  rfl

theorem mid_embMat : d.i₀ᴴ * V.gram * embMat d dH = 0 := by
  rw [embMat, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.i₀e, d.i₀e', Matrix.zero_mul,
    Matrix.zero_mul, add_zero]

end Emb

section Form

variable {V V' H Z : HSp D} {r : ℕ} (d : HypDec V V' r) (dH : HypDec H Z r) (W : HSp D)

theorem hO_rank_zero (hZ : Z.rank = 0) (x y : WO Z W) : hO Z W x y = 0 := by
  haveI : IsEmpty (Fin Z.rank) := by
    rw [hZ]
    infer_instance
  rw [GlobalTheory.MixModel.hO_eq_trace]
  simp [Matrix.trace]

theorem mul_embMat_jX (x : WO V W) : x * rat (embMat d dH) * dH.jX = x * d.jX := by
  rw [Matrix.mul_assoc]
  congr 1
  show rat (embMat d dH) * rat dH.e = rat d.e
  rw [← GlobalTheory.MixModel.rat_mul, embMat_e]

theorem mul_embMat_jY (x : WO V W) : x * rat (embMat d dH) * dH.jY = x * d.jY := by
  rw [Matrix.mul_assoc]
  congr 1
  show rat (embMat d dH) * rat dH.e' = rat d.e'
  rw [← GlobalTheory.MixModel.rat_mul, embMat_e']

theorem hO_split (hZ : Z.rank = 0) (x y : WO V W) :
    hO V W x y = hO V' W (x * rat d.i₀) (y * rat d.i₀) + hO H W (x * rat (embMat d dH)) (y * rat (embMat d dH)) := by
  rw [GlobalTheory.MixModel.HypDec.hO_coordS d, GlobalTheory.MixModel.HypDec.hO_coordS dH, hO_rank_zero W hZ,
    mul_embMat_jX d dH W x, mul_embMat_jX d dH W y, mul_embMat_jY d dH W x, mul_embMat_jY d dH W y]
  show _ = hO V' W (x * d.j0) (y * d.j0) + _
  abel

theorem symplOH_split (hZ : Z.rank = 0) (x y : WO V W) :
    symplOH V W x y =
      symplOH V' W (sandwich (rat 1) (rat d.i₀) x) (sandwich (rat 1) (rat d.i₀) y) +
        symplOH H W (sandwich (rat 1) (rat (embMat d dH)) x) (sandwich (rat 1) (rat (embMat d dH)) y) := by
  simp only [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.sandwich_apply, GlobalTheory.MixModel.rat_one, Matrix.one_mul]
  rw [hO_split d dH W hZ, map_add (f := _)]

end Form

section Res

variable {V V' H Z W : HSp D} {r : ℕ} (d : HypDec V V' r) (dH : HypDec H Z r)

theorem sand_B (y : Mx D W.rank r) (x : WO V' W) :
    sandwich (rat 1) (rat d.i₀) (isoPart V W d.e y + midPart V V' W d.i₀ x) = x := by
  have hadj : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D A = Aᴴ :=
    fun A => GlobalTheory.MixModel.cT_sig A
  have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * V.gram).map (incA D) * rat d.i₀ = 0 := by
    show rat (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * V.gram) * rat d.i₀ = 0
    rw [← GlobalTheory.MixModel.rat_mul, hadj, Matrix.mul_assoc, ei₀_assoc d, GlobalTheory.MixModel.rat_zero]
  have h2 : (V'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.i₀ * V.gram).map (incA D) * rat d.i₀ = 1 := by
    show rat (V'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.i₀ * V.gram) * rat d.i₀ = 1
    rw [← GlobalTheory.MixModel.rat_mul, hadj, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc d.i₀ᴴ, d.iso,
      Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V'), GlobalTheory.MixModel.rat_one]
  rw [GlobalTheory.MixModel.sandwich_apply, GlobalTheory.MixModel.rat_one, Matrix.one_mul, Matrix.add_mul]
  unfold isoPart midPart
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, h2, Matrix.mul_zero, Matrix.mul_one, zero_add]

theorem sand_A (y : Mx D W.rank r) (x : WO V' W) :
    sandwich (rat 1) (rat (embMat d dH)) (isoPart V W d.e y + midPart V V' W d.i₀ x) = isoPart H W dH.e y := by
  have hadj : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D A = Aᴴ :=
    fun A => GlobalTheory.MixModel.cT_sig A
  have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * V.gram).map (incA D) * rat (embMat d dH) =
      (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D dH.e * H.gram).map (incA D) := by
    show rat (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * V.gram) * rat (embMat d dH) = rat (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D dH.e * H.gram)
    rw [← GlobalTheory.MixModel.rat_mul, hadj, hadj, iso_embMat]
  have h2 : (V'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.i₀ * V.gram).map (incA D) * rat (embMat d dH) = 0 := by
    show rat (V'.gram⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.i₀ * V.gram) * rat (embMat d dH) = 0
    rw [← GlobalTheory.MixModel.rat_mul, hadj, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc d.i₀ᴴ, mid_embMat,
      Matrix.mul_zero, GlobalTheory.MixModel.rat_zero]
  rw [GlobalTheory.MixModel.sandwich_apply, GlobalTheory.MixModel.rat_one, Matrix.one_mul, Matrix.add_mul]
  unfold isoPart midPart
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, h2, Matrix.mul_zero, add_zero]

theorem surj_core (hZ : Z.rank = 0) (hsH : IsIsoSplit H Z dH.e dH.i₀) (ψ : AddChar (AF D.host.F) ℂ)
    (hψ : IsStdChar D ψ (-1)) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (hμ : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨) (f' : WO V' W → ℂ) (hf' : IsThetaFunO ψ V' W f') :
    ∃ f, IsThetaFunO ψ V W f ∧ f' = res V V' W d.e d.i₀ μ 𝓨 f := by
  obtain ⟨fH, hfH, hne⟩ := (GlobalTheory.TowerRestrict.res_theta D H Z W r dH.e dH.i₀ hsH ψ hψ μ 𝓨 hμ).2
  generalize hcv : res H Z W dH.e dH.i₀ μ 𝓨 fH 0 = c
  have hc : c ≠ 0 := by
    rintro rfl
    apply hne
    funext z
    have hz : z = 0 := by
      haveI : IsEmpty (Fin Z.rank) := by
        rw [hZ]
        infer_instance
      exact Matrix.ext fun _ j => isEmptyElim j
    subst hz
    exact hcv
  have hint : ∫ y in 𝓨, fH (isoPart H W dH.e y) ∂μ = c := by
    rw [← hcv]
    simp only [res, GlobalTheory.TowerRestrict.midPart_zero, add_zero]
  refine ⟨fun w => f' (sandwich (rat 1) (rat d.i₀) w) * (c⁻¹ • fH) (sandwich (rat 1) (rat (embMat d dH)) w), ?_, ?_⟩
  · exact GlobalTheory.MixModel.isThetaFunO_prod 1 d.i₀ 1 (embMat d dH) (symplOH_split d dH W hZ) hf'
      (GlobalTheory.OrientedHeis.theta_smul c⁻¹ hfH)
  · funext x
    simp only [res, sand_B, sand_A, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, integral_const_mul, hint, inv_mul_cancel₀ hc, mul_one]

private theorem isIsoSplit_of_hypDec {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (hρ : 0 < ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit S S₀ d.e d.i₀ := by
  have hadj : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D A = Aᴴ :=
    fun A => GlobalTheory.MixModel.cT_sig A
  refine ⟨⟨hρ, ?_, ?_⟩, ?_, ?_, d.rank_add.symm.trans (Nat.add_comm _ _ ▸ rfl)⟩
  · apply Fintype.linearIndependent_iff.2
    intro g hg
    have h1 : d.e.mulVec g = 0 := by
      funext k
      have hk := congrFun hg k
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply, smul_eq_mul, Pi.zero_apply] at hk
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← hk]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h2 : (d.e'ᴴ * S.gram * d.e).mulVec g = 0 := by
      rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
    rw [d.e'e, Matrix.one_mulVec] at h2
    exact fun i => congrFun h2 i
  · rw [GlobalTheory.MixModel.cT_sig]
    exact d.ee
  · rw [hadj]
    exact d.iso
  · rw [hadj, Matrix.mul_assoc]
    exact ei₀_assoc d

end Res

theorem res_surjective : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ f', IsThetaFunO ψ V' W f' → ∃ f, IsThetaFunO ψ V W f ∧ f' = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs ψ hψ μ 𝓨 hμ f' hf'
  obtain ⟨d, hdC, hdB, -⟩ := GlobalTheory.T.exists_wittDecomposition_isotropicSplit_unipotent D V V' r C B hs
  subst hdC hdB
  exact surj_core d (GlobalTheory.Core.Rk.SWLaw.dblDec (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral r)) rfl
    (isIsoSplit_of_hypDec _ hs.frame.1) ψ hψ μ 𝓨 hμ f' hf'

end GlobalTheory.TowerSurj

end
