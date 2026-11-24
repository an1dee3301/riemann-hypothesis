module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestrictionStatement
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
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
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
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
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

namespace I195MixedCoordinates_496aa803720ccf0c37cbff80

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_496aa803720ccf0c37cbff80

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.WMove

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → ∀ x : Mx D T.rank ρ, (∀ h, (_root_.I195MixedCoordinates_496aa803720ccf0c37cbff80.source d) T ψ μ 𝓕 (om (1, h) f) x = (_root_.I195MixedCoordinates_496aa803720ccf0c37cbff80.source d) T ψ μ 𝓕 (om (1, h) (heisO ψ S T (d.extX T (mt T h⁻¹ ⬝ x)) f)) 0) ∧ (∀ a g, (_root_.I195MixedCoordinates_496aa803720ccf0c37cbff80.source d) T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) x = (_root_.I195MixedCoordinates_496aa803720ccf0c37cbff80.source d) T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) (heisO ψ S T (d.extX T (x ⬝ a.1)) f)) 0) ∧ ∀ n : GA D S, (_root_.I195MixedCoordinates_496aa803720ccf0c37cbff80.source d) T ψ μ 𝓕 (om (n, 1) f) x = (_root_.I195MixedCoordinates_496aa803720ccf0c37cbff80.source d) T ψ μ 𝓕 (om (n, 1) (heisO ψ S T (d.extX T x ⬝ mt S n) f)) 0 := by
  intro D ψ S S₀ T ρ d χS χT om hω μ 𝓕 hμ f hf x
  have hb := fun F y => ((GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d).2.2.2.2.2.2.1 μ 𝓕 F y)
  change ∀ (F : WO S T → ℂ) (y : Mx D T.rank ρ),
    I195MixedCoordinates_496aa803720ccf0c37cbff80.source d T ψ μ 𝓕 F y =
      I195MixedCoordinates_496aa803720ccf0c37cbff80.source d T ψ μ 𝓕 (heisO ψ S T (d.extX T y) F) 0 at hb
  refine ⟨fun h => ?_, fun a g => ?_, fun n => ?_⟩
  · rw [hb, hω.om_heis _ _ _ _ hf]
    congr 3
    rw [actO_eq, inv_one, mt_one, Matrix.mul_one, HypDec.extX_apply, HypDec.extX_apply, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]
  · rw [hb, hω.om_heis _ _ _ _ hf]
    congr 3
    rw [actO_eq, mt_one, Matrix.one_mul, _root_.mul_inv_rev, ← map_inv d.levi, ← map_inv d.emb0, mt_mul,
      ← Matrix.mul_assoc, d.extX_apply T (x ⬝ a.1), Matrix.mul_assoc _ d.pX, d.wittDecomp_projX_anisotropicEmbedding, ← d.extX_apply T (x ⬝ a.1),
      d.extX_levi, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  · rw [hb, hω.om_heis _ _ _ _ hf]
    congr 3
    rw [actO_eq, mt_one, Matrix.one_mul, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]

end GlobalTheory.WMove
