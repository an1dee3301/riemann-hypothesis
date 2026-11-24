module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupActionFourierBesselBasePointStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalOrbitPointEqBesselBasePointStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalOrbitPointEqBesselBasePoint
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroup
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.ByCases
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

variable {D : D7} {σ : ℕ}

def eLast (D : D7) (ρ : ℕ) : Fin ρ → D.host.E := fun i => if i.1 + 1 = ρ then 1 else 0

theorem ratV_eLast (ρ : ℕ) : ratV (eLast D ρ) = ell D ρ := by
  funext i
  simp only [ratV, eLast, ell]
  split_ifs <;> simp

def zlQ (B : BesLev D σ) : Matrix (Fin B.L.rank) (Fin (σ + 1)) D.host.E := vecMulVec B.ζ (eLast D (σ + 1))

theorem rat_zlQ (B : BesLev D σ) : (rat (zlQ B) : Mx D B.L.rank (σ + 1)) = zl B := by
  rw [zl, zEll, ← ratV_eLast]
  funext i j
  simp [rat, zlQ, vecMulVec_apply, ratV]

theorem rat_gramQ (W : HSp D) {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) :
    (rat (gramQ W x) : Mx D ρ ρ) = adj (rat x) ⬝ (gA W ⬝ rat x) := by
  rw [gramQ, rat_mul, rat_mul, rat_conjTranspose]; rfl

theorem gramQ_eq_of_gramSkew {W W' : HSp D} {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E)
    (x' : Matrix (Fin W'.rank) (Fin ρ) D.host.E)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W (rat x : Mx D W.rank ρ) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W' (rat x')) :
    gramQ W x = gramQ W' x' := by
  have hu : IsUnit (-incA D D.host.xi0) :=
    ((isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map (incA D)).neg
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew at h
  rw [hu.smul_left_cancel, Matrix.transpose_inj] at h
  apply rat_injective
  rw [rat_gramQ, rat_gramQ, h]

theorem pairS_mul (T : HSp D) {ρ : ℕ} (x : Mx D T.rank ρ) (c : Mx D ρ ρ) :
    pairS T x (x ⬝ c) = (adj c ⬝ (adj x ⬝ (gA T ⬝ x))).trace := by
  rw [pairS, adj_mul, Matrix.mul_assoc]

theorem gramQ_zlQ_mulVec_last (B : BesLev D σ) (a : Fin (σ + 1) → D.host.E) :
    (gramQ B.L (zlQ B) *ᵥ a) (Fin.last σ) = (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ) * a (Fin.last σ) := by
  simp only [gramQ, zlQ, Matrix.mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, vecMulVec_apply, eLast,
    Pi.star_apply, Fin.val_last]
  simp only [if_true, mul_one, star_one]
  rw [Finset.sum_eq_single (Fin.last σ)]
  · simp only [Fin.val_last, if_true, mul_one]
  · intro b _ hb
    have hb' : ¬ (b.1 + 1 = σ + 1) := fun h => hb (Fin.ext (by simp only [Fin.val_last]; omega))
    simp only [hb', if_false, mul_zero, Finset.sum_const_zero, zero_mul]
  · simp

theorem basePoint_spec : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∃ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E,
    (rat x₀ : Mx D B.V.rank (σ + 1)) = x0 B ∧ IsBase B.V x₀ ∧
    Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) = besGrp B.d B.o ∧
    (∀ a : Fin (σ + 1) → D.host.E, gramQ B.V x₀ *ᵥ a = 0 → a (Fin.last σ) = 0) ∧
    ∀ (S S₀ : HSp D) (d : HypDec S S₀ (σ + 1)) (c : skewA D (σ + 1)), d.qS B.V c (x0 B) = d.qS B.L c (zl B) := by
  intro D σ B
  obtain ⟨x, ⟨hli, hg⟩, hx⟩ := GlobalTheory.T.exists_mem_orb_rat_eq_x0 D σ B
  rw [← rat_zlQ] at hg
  have hG : gramQ B.V x = gramQ B.L (zlQ B) := gramQ_eq_of_gramSkew x (zlQ B) hg
  have hA : adj (x0 B) ⬝ (gA B.V ⬝ x0 B) = adj (zl B) ⬝ (gA B.L ⬝ zl B) := by
    rw [← hx, ← rat_zlQ, ← rat_gramQ, ← rat_gramQ, hG]
  refine ⟨x, hx, ⟨hli, fun u hu => ?_⟩, ?_, fun a ha => ?_, fun S S₀ d c => ?_⟩
  · rw [rat_gramQ, hx, hA, ]
    have hz : zl B ⬝ u.1 = zl B := zEll_mul B.L B.ζ hu
    calc adj u.1 ⬝ (adj (zl B) ⬝ (gA B.L ⬝ zl B) ⬝ u.1) = adj (zl B ⬝ u.1) ⬝ (gA B.L ⬝ (zl B ⬝ u.1)) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = adj (zl B) ⬝ (gA B.L ⬝ zl B) := by rw [hz]
  · ext g
    rw [hx]
    exact ((GlobalTheory.T.mem_besGrp_iff_mt_mul_x0_eq_x0_mul D σ B).1 g).symm
  · have h1 := congrFun ha (Fin.last σ)
    rw [hG, gramQ_zlQ_mulVec_last, Pi.zero_apply] at h1
    exact (mul_eq_zero.1 h1).resolve_left B.line.2
  · rw [HypDec.qS, HypDec.qS, HypDec.symplOH_extX_extY, HypDec.symplOH_extX_extY, pairS_mul, pairS_mul, hA]

end GlobalTheory.Unf.FB
