module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SwapAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_one_mul (v : Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  have h1 : ∀ z : AF F, At (evFin F v) z → GlobalTheory.LatVac.liftV v 1 * z = z := by
    intro z hz
    have := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [smul_eq_mul] at this
    linear_combination -this
  have h2 := GlobalTheory.LatVac.at_liftV v 1 (b - GlobalTheory.LatVac.liftV v (evFin F v b))
    (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [smul_eq_mul] at h2
  have h3 := h1 _ (GlobalTheory.LatVac.at_liftV v (evFin F v b))
  linear_combination h2 + h3

omit [NumberField E] in
theorem smul_eq_map (v : Pl (F := F)) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • a =
      TensorProduct.map (GlobalTheory.LatVac.liftV v) LinearMap.id (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, hx, hy, map_add (f := _), map_add (f := _)]
  | tmul x b =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]
    simp [compFin, Algebra.TensorProduct.map_tmul]

theorem eq_zero_of_piW {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)}
    (ha : GlobalTheory.LatVac.liftV v (1 : Fv F v) • a = a) (h1 : piW t a = 0) (h2 : piW (t.comp σ) a = 0) : a = 0 := by
  have h0 : compFin F E v a = 0 :=
    split_ext h t (by rw [map_zero]; exact h1) (by rw [map_zero]; exact h2)
  rw [← ha, smul_eq_map, h0, map_zero]

omit [NumberField E] in
theorem one_sub_smul {m n : Type} {v : Pl (F := F)} {u : Matrix m n (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hu : At (evFin F v) u) :
    (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • u = 0 :=
  hu _ (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])



end GlobalTheory.SwapAtPlace
