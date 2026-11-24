module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionLemmaOfWittCoreDescentStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRational
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryTransvectionUnitaryAndConjugation
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalComplementIsotropicSandwich
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
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Ext
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
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
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
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

variable {D : D7}

theorem form_mulVec_mulVec (S : HSp D) {k l : ℕ} (M : Mx D S.rank k) (N : Mx D S.rank l) (x : Fin k → AE D)
    (y : Fin l → AE D) :
    form S (M *ᵥ x) (N *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj N ⬝ (gA S ⬝ M)) *ᵥ x) := by
  have h : (fun i => cA D ((N *ᵥ y) i)) = (N.map (cA D)) *ᵥ fun i => cA D (y i) := by
    funext i
    exact RingHom.map_mulVec (cA D) N y i
  rw [form, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec _ (adj N), adj,
    Matrix.vecMul_transpose]

theorem form_act_act (S : HSp D) (g : GA D S) (x y : VA S) : form S (act S g x) (act S g y) = form S x y := by
  rw [act, act, form_mulVec_mulVec, mt_unitary, form]

theorem act_vecX_of_mem_Nfix {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (j : Fin ρ) (a : Fin ρ → AE D)
    (ha : ∀ i, j < i → a i = 0) {m : GA D V} (hm : m ∈ Nfix d j) : act V m (vecX d a) = vecX d a := by
  have hm' : ∀ i : Fin ρ, i ≤ j → ∀ k, (mt V m ⬝ d.jX : Mx D V.rank ρ) k i = d.jX k i := by
    intro i hi k
    have h1 := (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hm).2) ⟨i, hi⟩
    have h2 := congrFun (congrFun (mem_fixer.1 h1) k) 0
    simpa [Matrix.mul_apply, Matrix.submatrix_apply] using h2
  rw [act, vecX, Matrix.mulVec_mulVec]
  funext k
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ≤ j
  · rw [hm' i hi k]
  · rw [ha i (not_le.1 hi), mul_zero, mul_zero]

theorem rat_mulVec_ratVec {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) (a : Fin n → D.host.E) :
    rat x *ᵥ ratVec a = ratVec (x *ᵥ a) := by
  funext i
  exact (RingHom.map_mulVec (incA D) x a i).symm

theorem transv_trivial_after_Nfix : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vS : VolM D W.rank ρ) (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → ∀ (j : Fin ρ) (a : Fin ρ → D.host.E), (∀ i, j < i → a i = 0) → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V) (u : GA D V), GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E, x *ᵥ a = 0 → ∀ m ∈ Nfix d j, ∀ n : GA D V, term ψ d W vS (om (m * u * n, 1) Ψ) x = term ψ d W vS (om (m * n, 1) Ψ) x := by
  intro D hD ψ V V₀ W ρ d χV χW om hW vS Ψ hΨ j a ha v u hv hu x hx m hm n
  obtain ⟨-, hConj, hTriv⟩ := GlobalTheory.T.transvectionLemma_of_wittCoreDescent D hD
  have ha' : ∀ i, j < i → ratVec a i = 0 := fun i hi => by simp [ratVec, ha i hi]
  have hmw : act V m (vecX d (ratVec a)) = vecX d (ratVec a) := act_vecX_of_mem_Nfix d j _ ha' hm
  have hc := hConj V V₀ ρ d (ratVec a) v hv u m hu
  rw [hmw] at hc
  have hv' : form V (vecX d (ratVec a)) (act V m v) = 0 := by
    rw [← hmw, form_act_act, hv]
  have hx' : rat x *ᵥ ratVec a = 0 := by
    rw [rat_mulVec_ratVec, hx]
    funext i
    simp [ratVec]
  have e : ((m * u * n, (1 : GA D W)) : GA D V × GA D W) = (m * u * m⁻¹, 1) * (m * n, 1) := by
    ext
    · simp [mul_assoc]
    · simp
  have key := hTriv V V₀ W ρ d ψ χV χW om hW vS.μ vS.𝓕 vS.covol a (act V m v) hv' (m * u * m⁻¹) hc (rat x) hx'
    (om (m * n, 1) Ψ) (hW.om_pres _ _ hΨ)
  rw [term, term, e, map_mul, Module.End.mul_apply]
  exact congrFun key 0

end GlobalTheory.Unf

end
