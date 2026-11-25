module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
public import Development.Core20Slim.CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.IdeleRoots.TorusPowers.HeckeTensor
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open PositivityTheory.RgEis PositivityTheory.RgEis.So
open NumberField
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.RgEisSo.Hd

theorem blg_of_dict : Dict → BLg := by
  intro hD F E _ _ _ _ _ σ χ c hσ _ _ _
  obtain ⟨-, -, -, -, h5⟩ := hD F E
  have key : ∀ x : (IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ, (adCM σ χ).lg x =
      Real.log (GlobalTheory.Doubling.absE F E x : ℝ) := fun x => by
    show Real.log (GroundTheory.Global.IdeleGroup.ideleModule E (Units.map (eqv F E).toRingHom.toMonoidHom x) : ℝ) = _
    rw [h5]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have e : Units.map (eqv F E).toRingHom.toMonoidHom (Units.map (nuCM F E).toMonoidHom x) =
        GroundTheory.Global.ideleEmbedding F E x := by
      apply Units.ext
      exact GroundTheory.BlockD.ThmBHecke.adeleEquiv_algebraMap (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)
    show Real.log (GroundTheory.Global.IdeleGroup.ideleModule E (Units.map (eqv F E).toRingHom.toMonoidHom (Units.map (nuCM F E).toMonoidHom x)) : ℝ) =
      2 * Real.log (GroundTheory.Global.IdeleGroup.ideleModule F x : ℝ)
    rw [e, ← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F),
      GroundTheory.Global.ideleNorm_ideleEmbedding, hσ.2.2.1, map_pow]
    have : (((GroundTheory.Global.IdeleGroup.ideleModule F x) ^ 2 : {r : ℝ // 0 < r}) : ℝ) =
      (GroundTheory.Global.IdeleGroup.ideleModule F x : ℝ) ^ 2 := rfl
    rw [this, Real.log_pow]
    norm_num
  · rw [key, key]
    have e : Units.map (adCM σ χ).σ.toMonoidHom x = GlobalTheory.Doubling.conjUnit σ x := by
      apply Units.ext
      rfl
    rw [e, GlobalTheory.Doubling.absE_conjUnit]
end GlobalTheory.CompanionTheory.RgEisSo.Hd
