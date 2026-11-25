module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.LinkSimil
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Unique
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.LinkGram

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj starAdj_ofAdj)

variable {D : D7}

theorem exists_inv_of_rank_one {m n : ℕ} (hm : m = 1) (hn : n = 1) (τ : Matrix (Fin m) (Fin n) D.host.E) (h : τ ≠ 0) :
    ∃ σ : Matrix (Fin n) (Fin m) D.host.E, σ * τ = 1 ∧ τ * σ = 1 := by
  subst hm; subst hn
  have hd : IsUnit τ.det := by
    rw [Matrix.det_unique, isUnit_iff_ne_zero]
    intro h0; apply h; ext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default, h0]; rfl
  exact ⟨τ⁻¹, Matrix.nonsing_inv_mul _ hd, Matrix.mul_nonsing_inv _ hd⟩

theorem scalar_one : incA D (-D.host.xi0⁻¹) * cA D (incA D D.host.xi0) = 1 := by
  have h := congrArg (cA D) (HypDec.wittDecomp_trace0Unit_mul_conj_neg_inv (D := D))
  rw [map_mul, map_one, cA_cA, mul_comm] at h
  exact h

theorem ofAdj_starAdj (L S : HSp D) (x : WO L S) : ofAdj L S (starAdj L S x) = x := by
  rw [starAdj, ofAdj, adj_smul, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    scalar_one, one_smul]
  simp only [Matrix.mul_assoc, giA_gA_cancel, giA_mul_gA, Matrix.mul_one]

theorem link_gram : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' →
    ∀ l : Link B L' ζ', l.τᴴ * (B.L.gram * l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram ∧
      ∀ S : HSp D, Function.Bijective (l.κ S) ∧
        ∀ w, l.κ S w ∈ ratMx D S.rank B.L.rank → w ∈ ratMx D L'.rank S.rank := by
  intro D ρ B L' ζ' h l
  refine ⟨by rw [Int.cast_one, one_mul]; exact GlobalTheory.Unf.StCheck.link_simil h l, fun S => ?_⟩
  have hτ : l.τ ≠ 0 := by
    intro h0
    have e := l.map
    rw [h0, Matrix.zero_mulVec] at e
    have hz : B.ζ = 0 := neg_eq_zero.mp e.symm
    apply B.line.2
    rw [hz]; simp
  obtain ⟨σ, hστ, hτσ⟩ := exists_inv_of_rank_one B.line.1 h.1 l.τ hτ
  have key : ∀ w, (rat σ : Mx D L'.rank B.L.rank) * starAdj B.L S (l.κ S w) = w := by
    intro w
    rw [Link.κ, starAdj_ofAdj, ← Matrix.mul_assoc, ← rat_mul, hστ, rat_one, Matrix.one_mul]
  refine ⟨⟨fun w w' e => by rw [← key w, ← key w', e], fun x => ⟨(rat σ : Mx D L'.rank B.L.rank) * starAdj B.L S x, ?_⟩⟩,
    fun w hw => ?_⟩
  · rw [Link.κ, ← Matrix.mul_assoc, ← rat_mul, hτσ, rat_one, Matrix.one_mul, ofAdj_starAdj]
  · rw [← key w]
    refine ratMx_mul (rat_mem σ) ?_
    obtain ⟨γ, hγ⟩ := mem_ratMx.1 hw
    rw [← hγ, starAdj, giA, gA, ← rat_conjTranspose, ← rat_mul, ← rat_mul, ← rat_smul]
    exact rat_mem _

end GlobalTheory.Unf.LinkGram
