module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaOfHeisenbergIntertwinerBoundedAtZeroStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositiStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOrthSummandSlicesSobolevBoundedStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.WeilSlice

variable {D : D7}

theorem symplOH_zero_right' (S T : HSp D) (x : WO S T) : symplOH S T x 0 = 0 := by
  simp [symplOH, symplO, hO]

theorem symplOH_zero_left' (S T : HSp D) (x : WO S T) : symplOH S T 0 x = 0 := by
  simp [symplOH, symplO, hO]

def shiftA {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) : WO S T →+ WO S T where
  toFun w := (o.resS T).symm (actO A T g⁻¹ h⁻¹ (o.resS T w).1, (o.resS T w).2)
  map_zero' := by simp [actO_eq]
  map_add' x y := by
    rw [map_add (f := _), Prod.fst_add, Prod.snd_add, ← map_add (f := _)]
    congr 1
    simp [actO_eq, Matrix.mul_add, Matrix.add_mul]

theorem shiftA_apply {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) (w : WO S T) :
    shiftA o T g h w = (o.resS T).symm (actO A T g⁻¹ h⁻¹ (o.resS T w).1, (o.resS T w).2) := rfl

theorem actO_shift (A T : HSp D) (g : GA D A) (h : GA D T) (u : WO A T) : actO A T g h (actO A T g⁻¹ h⁻¹ u) = u := by
  simp only [actO_eq, inv_inv, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (mt T h), mt_mul_inv, Matrix.one_mul, mt_mul_inv, Matrix.mul_one]

theorem continuous_shiftA {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) :
    Continuous (shiftA o T g h) := by
  have h1 : Continuous fun w : WO S T => (o.resS T w).1 := continuous_fst.comp (o.continuous_resS T)
  have h2 : Continuous fun w : WO S T => (o.resS T w).2 := continuous_snd.comp (o.continuous_resS T)
  refine (o.continuous_resS_symm T).comp (Continuous.prodMk ?_ h2)
  simp only [actO_eq]
  exact (continuous_const.matrix_mul h1).matrix_mul continuous_const

theorem shiftA_fin {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) (w : WO S T)
    (hw : w.map (finPart D) = 0) : (shiftA o T g h w).map (finPart D) = 0 := by
  rw [shiftA_apply, OrthDec.resS_symm_apply]
  simp only [OrthDec.resS_apply, actO_eq]
  rw [Matrix.map_add _ (map_add (finPart D))]
  simp only [Matrix.map_mul, hw, Matrix.zero_mul, Matrix.mul_zero, zero_add]

theorem shiftA_inf {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (g : GA D A) (h : GA D T) (w : WO S T)
    (hw : w.map (infPart D) = 0) : (shiftA o T g h w).map (infPart D) = 0 := by
  rw [shiftA_apply, OrthDec.resS_symm_apply]
  simp only [OrthDec.resS_apply, actO_eq]
  rw [Matrix.map_add _ (map_add (infPart D))]
  simp only [Matrix.map_mul, hw, Matrix.zero_mul, Matrix.mul_zero, zero_add]

theorem half (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) (χ χ' : (AE D)ˣ →* Circle) (om : Om A T) (hom : IsWeilDatumO ψ A T χ χ' om)
    (p : GA D A × GA D T) :
    IsThetaFunO ψ S T fun x => om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1 := by
  obtain ⟨g, h⟩ := p
  have hstd := hom.std
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hslice := (GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hstd S A B T o).2.2.2
  have hsob := (GlobalTheory.T.weil_operator_orth_summand_slices_sobolev_bounded D ψ θ hθ S A B T o).1 χ χ' om hom (g, h)
  refine GlobalTheory.T.theta_of_heisenberg_intertwiner_bounded_at_zero D ψ hstd θ hθ S T S T (shiftA o T g h) (continuous_shiftA o T g h) (shiftA_fin o T g h)
    (shiftA_inf o T g h) (fun F x => om (g, h) (fun u => F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1)
    ?_ ?_ ?_ f hf
  · have e : (fun F : WO S T → ℂ => om (g, h) (fun u => F ((o.resS T).symm (u, (o.resS T 0).2))) (o.resS T 0).1) =
        fun F => om (g, h) (fun u => F ((o.resS T).symm (u, 0))) 0 := by
      funext F
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero]
    exact e ▸ hsob
  · intro F w hF
    funext x
    have hG := (hslice F hF).1 ((o.resS T x).2 + (o.resS T w).2)
    have hin : (fun u => heisO ψ S T (shiftA o T g h w) F ((o.resS T).symm (u, (o.resS T x).2))) =
        ψ (symplOH B T (o.resS T x).2 (o.resS T w).2) • heisO ψ A T (actO A T g⁻¹ h⁻¹ (o.resS T w).1)
          (fun u => F ((o.resS T).symm (u, (o.resS T x).2 + (o.resS T w).2))) := by
      funext u
      simp only [heisO, shiftA_apply, Pi.smul_apply, smul_eq_mul]
      rw [o.symplOH_resS]
      simp only [AddEquiv.apply_symm_apply]
      rw [← map_add (f := _), Prod.mk_add_mk, AddChar.map_add_eq_mul]
      ring
    show om (g, h) (fun u => heisO ψ S T (shiftA o T g h w) F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1 = _
    rw [hin, map_smul, hom.om_heis g h _ _ hG, actO_shift]
    simp only [Pi.smul_apply, heisO, smul_eq_mul]
    rw [o.symplOH_resS, map_add (o.resS T) x w, AddChar.map_add_eq_mul]
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  · intro F γ hF
    have hr : ratW T S γ ∈ ratL T S := ⟨γ, rfl⟩
    obtain ⟨ha, hb⟩ := (o.mem_ratL_resS T _).1 hr
    have hsl : (fun u => F ((o.resS T).symm (u, (o.resS T (ratW T S γ)).2))) =
        fun u => F ((o.resS T).symm (u, 0)) := by
      funext u
      have hb' : (o.resS T).symm (0, (o.resS T (ratW T S γ)).2) ∈ ratL T S := by
        refine (o.mem_ratL_resS T _).2 ?_
        simp only [AddEquiv.apply_symm_apply]
        exact ⟨zero_mem _, hb⟩
      obtain ⟨δ, hδ⟩ := hb'
      have hδ' : ratW T S δ = (o.resS T).symm (0, (o.resS T (ratW T S γ)).2) := hδ
      have e : (o.resS T).symm (u, (o.resS T (ratW T S γ)).2) = ratW T S δ + (o.resS T).symm (u, 0) := by
        rw [hδ', ← map_add (f := _), Prod.mk_add_mk, zero_add, add_zero]
      rw [e, hF.quasi δ, hδ', o.symplOH_resS]
      simp only [AddEquiv.apply_symm_apply, symplOH_zero_left', symplOH_zero_right', add_zero, neg_zero,
        AddChar.map_zero_eq_one, one_mul]
    show om (g, h) (fun u => F ((o.resS T).symm (u, (o.resS T (ratW T S γ)).2))) (o.resS T (ratW T S γ)).1 =
      om (g, h) (fun u => F ((o.resS T).symm (u, (o.resS T 0).2))) (o.resS T 0).1
    simp only [map_zero, Prod.fst_zero, Prod.snd_zero]
    rw [hsl]
    obtain ⟨γa, hγa⟩ := ha
    have ea : (o.resS T (ratW T S γ)).1 = ratW T A γa + 0 := by rw [add_zero]; exact hγa.symm
    rw [ea, (hom.om_pres (g, h) _ ((hslice F hF).1 0)).quasi γa 0, symplOH_zero_right', neg_zero,
      AddChar.map_zero_eq_one, one_mul]

theorem resS_symm_swap {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (u : WO B T) (v : WO A T) :
    (o.symm.resS T).symm (u, v) = (o.resS T).symm (v, u) := by
  rw [OrthDec.resS_symm_apply, OrthDec.resS_symm_apply]; exact add_comm _ _

theorem weilSlice_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ p, IsThetaFunO ψ S T fun x => om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1) ∧ ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om B T), IsWeilDatumO ψ B T χ χ' om → ∀ p, IsThetaFunO ψ S T fun x => om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2 := by
  intro D ψ S A B T o f hf
  refine ⟨fun χ χ' om hom p => half D ψ S A B T o f hf χ χ' om hom p, fun χ χ' om hom p => ?_⟩
  have h2 := half D ψ S B A T o.symm f hf χ χ' om hom p
  have key : (fun x => om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2) =
      fun x => om p (fun u => f ((o.symm.resS T).symm (u, (o.symm.resS T x).2))) (o.symm.resS T x).1 := by
    funext x
    simp only [resS_symm_swap]
    rfl
  exact key ▸ h2

end GlobalTheory.WeilSlice
