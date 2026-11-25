module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdeleAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsStdIsVacVec
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeLeRealSymplecticPairingSum
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
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
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealEqWeil

theorem weilDatum_realEq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om om' : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om' → (∀ τ, ∃ e : ℚ, HasInfExp D χS τ e ∧ HasInfExp D χS' τ e) → (∀ τ, ∃ e : ℚ, HasInfExp D χT τ e ∧ HasInfExp D χT' τ e) → ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ f, IsThetaFunO ψ S T f → om (a, b) f = om' (a, b) f := by
  intro D ψ S T χS χT χS' χT' om om' hW hW' hS hT a ha b hb f hf
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D

  have eS : ∀ τ, HasInfExp D (χS' * χS⁻¹) τ ((0 : ℤ) : ℚ) := fun τ => by
    obtain ⟨e, h1, h2⟩ := hS τ
    simpa using GlobalTheory.Chain.hasInfExp_div h2 h1
  have eT : ∀ τ, HasInfExp D (χT' * χT⁻¹) τ ((0 : ℤ) : ℚ) := fun τ => by
    obtain ⟨e, h1, h2⟩ := hT τ
    simpa using GlobalTheory.Chain.hasInfExp_div h2 h1
  obtain ⟨om'', hW'', hmv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ hW.std S T χS χT (χS' * χS⁻¹) (χT' * χT⁻¹) om hW
    (GlobalTheory.WeilVacChar.hecke_mul_inv hW'.hecS hW.hecS) (GlobalTheory.WeilVacChar.hecke_mul_inv hW'.hecT hW.hecT)
    (GlobalTheory.WeilVacChar.resEta_mul_inv hW'.resS hW.resS) (GlobalTheory.WeilVacChar.resEta_mul_inv hW'.resT hW.resT)
  rw [GlobalTheory.WeilVacChar.mul_mul_inv_cancel, GlobalTheory.WeilVacChar.mul_mul_inv_cancel] at hW''
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ S (GlobalTheory.RealPairBound.gramAt_det_ne D S) a ha
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ T (GlobalTheory.RealPairBound.gramAt_det_ne D T) b hb
  have x1 : (χT' * χT⁻¹) x = 1 := by
    apply Circle.coe_injective
    rw [hxv _ (fun _ => 0) eT]
    simp
  have y1 : (χS' * χS⁻¹) y = 1 := by
    apply Circle.coe_injective
    rw [hyv _ (fun _ => 0) eS]
    simp
  have h1 := hmv a b x y hx hy
  rw [x1, y1, inv_one, one_mul, Circle.coe_one, one_smul] at h1
  rw [← h1]
  exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hW.std S T χS' χT' om'' om' hW'' hW' (a, b) f hf

end GlobalTheory.RealEqWeil
