module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
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
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
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
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.RatBlock

variable {D : D7}

theorem blockX_mem_UX {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {n : GA D V} (hn : n ∈ flagN d) :
    ∃ u ∈ UX D ρ, blockX d n = u.1 := by
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D V V₀ ρ d).1 n).1 hn
  have h1 : mt V (d.levi u * (d.nB b * d.nC c)) ⬝ d.jX = d.jX ⬝ u.1 := by
    rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX]
  refine ⟨u, hu, ?_⟩
  rw [blockX, h1, ← Matrix.mul_assoc d.pX d.jX, d.pX_jX, Matrix.one_mul]

theorem blockX_col_of_fix {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {g : GA D V} (k : Fin ρ)
    (h : g ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => k)) (i : Fin ρ) :
    blockX d g i k = (1 : Mx D ρ ρ) i k := by
  have hcol : ∀ l, (mt V g ⬝ d.jX) l k = d.jX l k := fun l => by
    have := congrFun (congrFun (mem_fixer.1 h) l) 0
    simpa [Matrix.mul_apply, Matrix.submatrix_apply] using this
  rw [← d.pX_jX, blockX, Matrix.mul_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [hcol l]

end GlobalTheory.Unf.RatBlock


open GlobalTheory.Unf.RatBlock in
theorem GlobalTheory.Unf.ratBlock_unitri : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (γ : GA D V), γ ∈ GQ V → γ ∈ flagN d → ∃ u u' : Matrix (Fin ρ) (Fin ρ) D.host.E, (rat u : Mx D ρ ρ) = blockX d γ ∧ u * u' = 1 ∧ u' * u = 1 ∧ (∀ i, u i i = 1) ∧ (∀ i k, k < i → u i k = 0) ∧ ∀ j : Fin ρ, γ ∈ Nfix d j → ∀ i k, k ≤ j → u i k = if i = k then 1 else 0 := by
  intro D V V₀ ρ d γ hq hn
  obtain ⟨M, hM⟩ := (mem_GQ_iff V γ).1 hq
  have hM' : rat M = mt V γ := hM
  have hb : (rat (d.qX * (M * d.e)) : Mx D ρ ρ) = blockX d γ := by
    rw [blockX, ← hM', rat_mul, rat_mul]; rfl
  obtain ⟨v, hv, hvb⟩ := blockX_mem_UX d hn
  have hent : ∀ i k, incA D ((d.qX * (M * d.e)) i k) = v.1 i k := fun i k => by
    have := congrFun (congrFun (hb.trans hvb) i) k
    exact this
  have hdiag : ∀ i, (d.qX * (M * d.e)) i i = 1 := fun i =>
    incA_injective (by rw [map_one, hent]; exact ((mem_UX.1 hv) i i).2)
  have hlow : ∀ i k, k < i → (d.qX * (M * d.e)) i k = 0 := fun i k hki =>
    incA_injective (by rw [map_zero, hent]; exact ((mem_UX.1 hv) i k).1 hki)
  have hdet : (d.qX * (M * d.e)).det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i k (hki : k < i) => hlow i k hki)]
    simp [hdiag]
  have hu : IsUnit (d.qX * (M * d.e)).det := by rw [hdet]; exact isUnit_one
  refine ⟨d.qX * (M * d.e), (d.qX * (M * d.e))⁻¹, hb, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu,
    hdiag, hlow, fun j hj i k hkj => ?_⟩
  have hfix : γ ∈ fixer V (d.jX.submatrix id fun _ : Fin 1 => k) := by
    have h2 := (Subgroup.mem_inf.1 hj).2
    exact (Subgroup.mem_iInf.1 h2) ⟨k, hkj⟩
  apply incA_injective
  have e1 := blockX_col_of_fix d k hfix i
  rw [← hb] at e1
  change incA D _ = _ at e1
  rw [e1, Matrix.one_apply]
  split_ifs <;> simp
