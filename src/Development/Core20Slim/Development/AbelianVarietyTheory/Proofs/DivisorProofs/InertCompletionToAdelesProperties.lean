module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InLat2
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixTrivialOffInertPlaceUnitaryAtPlace
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Function
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertBigCell

theorem iotaW_adelic_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {v : Pl (F := F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  Function.Injective (GlobalTheory.InertBigCell.iotaW hw) ∧
  (∀ x y, GlobalTheory.InertBigCell.iotaW hw (x * y) = GlobalTheory.InertBigCell.iotaW hw x * GlobalTheory.InertBigCell.iotaW hw y) ∧
  GlobalTheory.InertBigCell.iotaW hw 1 = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) ∧
  (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, GlobalTheory.InertBigCell.iotaW hw x = z) ∧
  (∀ x, GlobalTheory.InertBigCell.iotaW hw (GlobalTheory.InertBigCell.conjW σ hw x) = cA σ (GlobalTheory.InertBigCell.iotaW hw x)) ∧
  (∀ x, GlobalTheory.InertBigCell.iotaW hw (2⁻¹ * x) = ⅟(2 : AF F) • GlobalTheory.InertBigCell.iotaW hw x) ∧
  (∀ e : E, GlobalTheory.InertBigCell.iotaW hw (algebraMap E (w.adicCompletion E) e) =
    algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) * inclR (F := F) (AF F) e) := by
  intro F E _ _ _ _ _ σ v w hw
  refine ⟨iotaW_injective hw, iotaW_mul hw, iotaW_one hw, fun z => ?_, iotaW_conjW σ hw, fun x => ?_,
    iotaW_algebraMap hw⟩
  · rw [GlobalTheory.InertLocField.at_iff v z]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨InertChart.complEquiv hw (under_eq_of_isInertAt hw) y, by
        rw [iotaW_apply, RingEquiv.symm_apply_apply]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, (iotaW_apply hw x).symm⟩
  · have h := invOf_two_smul_add_iotaW hw 0 x
    rw [add_zero, zero_add, zero_add] at h
    exact h.symm

end GlobalTheory.InertBigCell
