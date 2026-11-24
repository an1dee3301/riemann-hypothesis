module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
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
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

variable {D : D7}

theorem linInd_e {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) : LinearIndependent D.host.E d.e.transpose := by
  show LinearIndependent D.host.E (fun i : Fin ρ => fun k : Fin W.rank => d.e k i)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : d.e *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← this]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h2 : (d.e'ᴴ * W.gram * d.e) *ᵥ g = 0 := by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
  rw [d.e'e, Matrix.one_mulVec] at h2
  intro i; exact congrFun h2 i

theorem gramQ_e {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) : gramQ W d.e = 0 := by
  rw [gramQ, ← Matrix.mul_assoc]; exact d.ee

theorem flagUnipotent_anisotropic_projection_eq_one {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) {n : GA D W} (hn : n ∈ flagN d) :
    d.p0 ⬝ (mt W n ⬝ d.j0) = 1 := by
  obtain ⟨u, -, b, c, rfl⟩ := ((flag_jacobi_structure D W W₀ ρ d).1 n).1 hn
  rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.wittDecomp_levi_inclAnisotropic,
    ← Matrix.mul_assoc (mt W (d.levi u)) d.jX, d.levi_jX, Matrix.mul_add, d.p0_j0, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, d.p0_jX, Matrix.zero_mul, Matrix.zero_mul, add_zero]

theorem Rgrp_eq {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) : Rgrp W (rat d.e) = jacGrp d := by
  have dec := flag_jacobi_structure D W W₀ ρ d
  ext r
  constructor
  · rintro ⟨u, hu, hr⟩
    have hs : d.levi u⁻¹ * r ∈ stabX d := by
      show mt W (d.levi u⁻¹ * r) ⬝ d.jX = d.jX
      rw [mt_mul, Matrix.mul_assoc, show mt W r ⬝ d.jX = d.jX ⬝ u.1 from hr, ← Matrix.mul_assoc, d.levi_jX,
        Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    obtain ⟨n, hn, h, he⟩ := (dec.2.2.1 _).1 hs
    have hl : d.levi u ∈ flagN d := (dec.1 _).2 ⟨u, hu, 0, 0, by rw [d.nB_zero, d.nC_zero, mul_one, mul_one]⟩
    refine (dec.2.2.2.1 r).2 ⟨d.levi u * n, mul_mem hl (Subgroup.mem_inf.1 hn).1, h, ?_⟩
    rw [mul_assoc, ← he, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  · intro hr
    obtain ⟨n, hn, h, rfl⟩ := (dec.2.2.2.1 r).1 hr
    obtain ⟨u, hu, b, c, rfl⟩ := (dec.1 n).1 hn
    refine ⟨u, hu, ?_⟩
    show mt W _ ⬝ d.jX = d.jX ⬝ u.1
    rw [mt_mul, mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.nC_jX, d.nB_jX,
      d.levi_jX]

theorem flagUnipotent_mul_emb_mem_rational_iff {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) {n : GA D W} (hn : n ∈ flagN d) (h : GA D W₀) :
    n * d.emb0 h ∈ GQ W ↔ n ∈ GQ W ∧ h ∈ GQ W₀ := by
  constructor
  · intro hg
    have hh : h ∈ GQ W₀ := by
      rw [mem_GQ_iff] at hg ⊢
      have e : mt W₀ h = d.p0 ⬝ (mt W (n * d.emb0 h) ⬝ d.j0) := by
        rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt W n), ← Matrix.mul_assoc, flagUnipotent_anisotropic_projection_eq_one d hn,
          Matrix.one_mul]
      rw [e]
      exact ratMx_mul (rat_mem _) (ratMx_mul hg (rat_mem _))
    refine ⟨?_, hh⟩
    have : n = n * d.emb0 h * (d.emb0 h)⁻¹ := by rw [mul_inv_cancel_right]
    rw [this]
    exact mul_mem hg (inv_mem (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hh))
  · rintro ⟨h1, h2⟩
    exact mul_mem h1 (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints h2)

theorem base_point : ∀ (D : D7) (W W₀ : HSp D) (ρ : ℕ) (d : HypDec W W₀ ρ), IsBase W d.e ∧ gramQ W d.e = 0 ∧ xZero d = rat d.e ∧ Rgrp W (rat d.e) = jacGrp d ∧ Continuous d.emb0 ∧ ∀ n ∈ flagN d, ∀ h, n * d.emb0 h ∈ GQ W ↔ n ∈ GQ W ∧ h ∈ GQ W₀ := by
  intro D W W₀ ρ d
  refine ⟨⟨linInd_e d, fun u _ => ?_⟩, gramQ_e d, rfl, Rgrp_eq d, d.continuous_embed, fun n hn h => flagUnipotent_mul_emb_mem_rational_iff d hn h⟩
  rw [gramQ_e d, rat_zero, Matrix.zero_mul, Matrix.mul_zero]

end GlobalTheory.Unf
