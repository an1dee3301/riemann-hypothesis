module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceCmHostAdeles
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataLevel
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
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
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
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.Reindex

variable {D : D7}

theorem exists_rat_block {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {γ : GA D V} (hq : γ ∈ GQ V)
    (hn : γ ∈ flagN d) : ∃ (u : UX D ρ) (u₀ : Matrix (Fin ρ) (Fin ρ) D.host.E),
      blockX d γ = u.1.1 ∧ rat u₀ = u.1.1 := by
  obtain ⟨u, hu, h⟩ := GlobalTheory.JacClosed.flagN_le d hn
  have hb : blockX d γ = u.1 := by rw [blockX, h, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
  have hr : blockX d γ ∈ ratMx D ρ ρ :=
    ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff V γ).1 hq) (rat_mem _))
  obtain ⟨u₀, hu₀⟩ := mem_ratMx.1 hr
  exact ⟨⟨u, hu⟩, u₀, hb, hu₀.trans hb⟩

theorem det_eq_one {ρ : ℕ} (u : UX D ρ) (u₀ : Matrix (Fin ρ) (Fin ρ) D.host.E) (h : rat u₀ = u.1.1) :
    u₀.det = 1 := by
  have h0 : ∀ i j : Fin ρ, j < i → u₀ i j = 0 := fun i j hij => incA_injective (by
    rw [map_zero]
    have := congrFun (congrFun h i) j
    change incA D (u₀ i j) = _ at this
    rw [this]; exact ((mem_UX.1 u.2) i j).1 hij)
  have h1 : ∀ i : Fin ρ, u₀ i i = 1 := fun i => incA_injective (by
    rw [map_one]
    have := congrFun (congrFun h i) i
    change incA D (u₀ i i) = _ at this
    rw [this]; exact ((mem_UX.1 u.2) i i).2)
  rw [Matrix.det_of_upperTriangular (fun i j (hij : j < i) => h0 i j hij)]
  simp [h1]

theorem gramQ_mul (W : HSp D) {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) (u₀ : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    gramQ W (x * u₀) = u₀ᴴ * gramQ W x * u₀ := by
  simp only [gramQ, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end GlobalTheory.Unf.Reindex


open GlobalTheory.Unf.Reindex in
theorem GlobalTheory.Unf.tsum_offBase_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ γ ∈ GQ V, γ ∈ flagN d → ∀ Φ : WO V W → ℂ, IsThetaFunO ψ V W Φ → ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS (om (γ, 1) Φ) x.1 = ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS Φ x.1 := by
  intro D ψ V V₀ W ρ d χV χW om om' hV hV₀ vS x₀ hx₀ γ hq hn Φ hΦ
  obtain ⟨u, u₀, hb, hu₀⟩ := exists_rat_block d hq hn
  have hdet : IsUnit u₀.det := by rw [det_eq_one u u₀ hu₀]; exact isUnit_one
  have hdet' : IsUnit u₀ᴴ.det := by rw [Matrix.det_conjTranspose, det_eq_one u u₀ hu₀, star_one]; exact isUnit_one
  set G₀ := gramQ W x₀
  have hG : u₀ᴴ * G₀ * u₀ = G₀ := by
    apply rat_injective
    have := hx₀.2 u.1 u.2
    rw [rat_mul, rat_mul, rat_conjTranspose, hu₀]
    rw [Matrix.mul_assoc]; exact this
  have key : ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E, gramQ W (x * u₀) = G₀ ↔ gramQ W x = G₀ := by
    intro x
    rw [gramQ_mul]
    constructor
    · intro h
      have h2 : u₀ᴴ * gramQ W x * u₀ = u₀ᴴ * G₀ * u₀ := h.trans hG.symm
      have h3 := congrArg (fun M => (u₀ᴴ)⁻¹ * M * u₀⁻¹) h2
      simp only [Matrix.mul_assoc] at h3
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet', Matrix.mul_nonsing_inv _ hdet] using h3
    · intro h; rw [h, hG]
  have hinv : u₀ * u₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hinv' : u₀⁻¹ * u₀ = 1 := Matrix.nonsing_inv_mul _ hdet
  let e : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ G₀} ≃
      {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ G₀} :=
    { toFun := fun x => ⟨x.1 * u₀, fun h => x.2 ((key x.1).1 h)⟩
      invFun := fun x => ⟨x.1 * u₀⁻¹, fun h => x.2 (by
        have := (key (x.1 * u₀⁻¹)).2 h
        rwa [Matrix.mul_assoc, hinv', Matrix.mul_one] at this)⟩
      left_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hinv, Matrix.mul_one])
      right_inv := fun x => Subtype.ext (by simp only [Matrix.mul_assoc, hinv', Matrix.mul_one]) }
  have hterm : ∀ x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ G₀},
      term ψ d W vS (om (γ, 1) Φ) x.1 = term ψ d W vS Φ (e x).1 := by
    intro x
    refine (GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hV hV₀ vS Φ hΦ).2.1 γ hq hn x.1 (x.1 * u₀) ?_
    rw [rat_mul, hu₀, hb]
  rw [tsum_congr hterm]
  exact Equiv.tsum_eq e (fun y => term ψ d W vS Φ y.1)

end
