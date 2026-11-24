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
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.ByCases
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBigCell

theorem idem_split_mul {R S : Type} [CommRing R] [Ring S] (e : R) (ι : S →+ R)
    (he : (1 - e) * (1 - e) = 1 - e) (hι : ∀ x, (1 - e) * ι x = 0) (hmul : ∀ x y, ι (x * y) = ι x * ι y)
    {l m n : Type} [Fintype m] (A : Matrix l m R) (B : Matrix m n R) (X : Matrix l m S) (Y : Matrix m n S) :
    ((1 - e) • A + X.map ι) * ((1 - e) • B + Y.map ι) = (1 - e) • (A * B) + (X * Y).map ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hmul]
  linear_combination (A i k * B k j) * he + A i k * hι (Y k j) + B k j * hι (X i k)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

theorem iotaW_apply (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    iotaW hw x = GlobalTheory.InertLocField.liftT E v ((InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm x) := rfl

theorem iotaW_injective (hw : Formalism.UG.IsInertAt F E v w) : Function.Injective (iotaW hw) :=
  (GlobalTheory.InertLocField.liftT_injective v).comp (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm.injective

theorem iotaW_mul (hw : Formalism.UG.IsInertAt F E v w) (x y : w.adicCompletion E) :
    iotaW hw (x * y) = iotaW hw x * iotaW hw y := by
  rw [iotaW_apply, iotaW_apply, iotaW_apply, map_mul, GlobalTheory.InertLocField.liftT_mul]

theorem idem_mul_iotaW (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) * iotaW hw x = iotaW hw x := by
  rw [← Algebra.smul_def, GlobalTheory.InertLocField.liftV_one_smul, iotaW_apply, GlobalTheory.InertLocField.evT_liftT]

theorem one_sub_mul_iotaW (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) * iotaW hw x = 0 := by
  rw [sub_mul, one_mul, idem_mul_iotaW, sub_self]

theorem one_sub_idem (v : Pl (F := F)) :
    (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) * (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) =
      1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) := by
  have h : algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) * algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) =
      algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) := by
    rw [← map_mul, ← GlobalTheory.InertLocField.liftV_mul, mul_one]
  linear_combination h

theorem complEquiv_symm_algebraMap' (hw : Formalism.UG.IsInertAt F E v w) (x : E) :
    (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm (algebraMap E _ x) = (1 : Fv F v) ⊗ₜ[F] x := by
  rw [RingEquiv.symm_apply_eq]
  change _ = toCompl (under_eq_of_isInertAt hw) ((1 : Fv F v) ⊗ₜ[F] x)
  rw [toCompl_tmul, map_one, one_mul]

theorem iotaW_algebraMap (hw : Formalism.UG.IsInertAt F E v w) (x : E) :
    iotaW hw (algebraMap E _ x) = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) * inclR (F := F) (AF F) x := by
  rw [iotaW_apply, complEquiv_symm_algebraMap', GlobalTheory.InertLocField.liftT_tmul]
  change _ = (GlobalTheory.LatVac.liftV v 1 ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] x)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem iotaW_conjW (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) (x : w.adicCompletion E) :
    iotaW hw (conjW σ hw x) = cA σ (iotaW hw x) := by
  rw [iotaW_apply, iotaW_apply, ← GlobalTheory.InertLocField.liftT_sigR]
  congr 1
  exact (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm_apply_apply _

theorem incM_split (hw : Formalism.UG.IsInertAt F E v w) {l m : Type} (J : Matrix l m E) :
    incM F J = (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • incM F J +
      (J.map (algebraMap E (w.adicCompletion E))).map (iotaW hw) := by
  ext i j
  simp only [incM, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, iotaW_algebraMap]
  ring

end GlobalTheory.InertBigCell

namespace GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

theorem iotaW_one (hw : Formalism.UG.IsInertAt F E v w) :
    iotaW hw 1 = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) := by
  rw [← map_one (algebraMap E (w.adicCompletion E)), iotaW_algebraMap]
  change _ * inclR (F := F) (AF F) 1 = _
  rw [(inclR (F := F) (AF F)).map_one, mul_one]

theorem diagCols_split (hw : Formalism.UG.IsInertAt F E v w) (ι : Type) [DecidableEq ι] :
    (diagCols ι : Matrix (ι ⊕ ι) ι (AE F E)) =
      (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (diagCols ι : Matrix (ι ⊕ ι) ι (AE F E)) +
        (diagCols ι : Matrix (ι ⊕ ι) ι (w.adicCompletion E)).map (iotaW hw) := by
  ext i j
  rcases i with i | i <;>
  · simp only [diagCols, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.one_apply]
    split_ifs
    · rw [iotaW_one]; ring
    · rw [map_zero]; ring

theorem invOf_two_smul_add_iotaW (hw : Formalism.UG.IsInertAt F E v w) (t : AE F E) (x : w.adicCompletion E) :
    ⅟(2 : AF F) • (t + t + iotaW hw x) = t + iotaW hw ((2 : w.adicCompletion E)⁻¹ * x) := by
  have h2 : (2 : w.adicCompletion E) ≠ 0 := by
    rw [← map_ofNat (algebraMap E (w.adicCompletion E)) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have hx : iotaW hw x = iotaW hw (2⁻¹ * x) + iotaW hw (2⁻¹ * x) := by
    rw [← map_add (f := _), ← add_mul, ← two_mul, mul_inv_cancel₀ h2, one_mul]
  rw [hx, show t + t + (iotaW hw (2⁻¹ * x) + iotaW hw (2⁻¹ * x)) =
      (2 : AF F) • (t + iotaW hw (2⁻¹ * x)) by rw [two_smul]; abel, smul_smul, invOf_mul_self, one_smul]

theorem glueW_transpose (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι (w.adicCompletion E)) : (glueW hw P)ᵀ = glueW hw Pᵀ := by
  rw [glueW, glueW, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_map]

theorem glueW_map_cA (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι (w.adicCompletion E)) : (glueW hw P).map (cA σ) = glueW hw (P.map (conjW σ hw)) := by
  ext i j
  simp only [glueW, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub,
    map_one, AlgHom.commutes, iotaW_conjW]
  congr 2
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem glueW_read_at_place (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι] :
  (∀ (J : Matrix ι ι E) (P : Matrix ι ι (w.adicCompletion E)),
    (GlobalTheory.InertBigCell.glueW hw P)ᵀ * incM F J * (GlobalTheory.InertBigCell.glueW hw P).map (cA σ) = incM F J ↔
      Pᵀ * J.map (algebraMap E (w.adicCompletion E)) * P.map (GlobalTheory.InertBigCell.conjW σ hw) = J.map (algebraMap E (w.adicCompletion E))) ∧
  (∀ P : Matrix (ι ⊕ ι) (ι ⊕ ι) (w.adicCompletion E), P * diagCols ι = diagCols ι →
    GlobalTheory.InertBigCell.glueW hw P * (diagCols ι : Matrix (ι ⊕ ι) ι (AE F E)) = diagCols ι) ∧
  (∀ P : Matrix (ι ⊕ ι) (ι ⊕ ι) (w.adicCompletion E),
    ⅟(2 : AF F) • ((GlobalTheory.InertBigCell.glueW hw P).toBlocks₁₁ + (GlobalTheory.InertBigCell.glueW hw P).toBlocks₁₂ +
      (GlobalTheory.InertBigCell.glueW hw P).toBlocks₂₁ + (GlobalTheory.InertBigCell.glueW hw P).toBlocks₂₂) =
    GlobalTheory.InertBigCell.glueW hw ((2 : w.adicCompletion E)⁻¹ • (P.toBlocks₁₁ + P.toBlocks₁₂ + P.toBlocks₂₁ + P.toBlocks₂₂))) := by
  set e := algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) with he_def
  refine ⟨fun J P => ?_, fun P hP => ?_, fun P => ?_⟩
  · rw [glueW_transpose, glueW_map_cA, glueW, glueW, incM_split hw J, idem_split_mul e (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw), idem_split_mul e (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw), Matrix.one_mul, Matrix.mul_one,
      add_right_inj]
    exact (Matrix.map_injective (iotaW_injective hw)).eq_iff
  · rw [diagCols_split hw ι, glueW, idem_split_mul e (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw),
      Matrix.one_mul]
    exact congrArg (fun M => (1 - e) • (diagCols ι : Matrix (ι ⊕ ι) ι (AE F E)) + M.map (iotaW hw)) hP
  · ext i j
    simp only [glueW, Matrix.smul_apply, Matrix.add_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
      Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.map_apply, smul_eq_mul, Matrix.one_apply, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, if_false, mul_zero, add_zero]
    rw [← invOf_two_smul_add_iotaW hw, map_add (f := _), map_add (f := _), map_add (f := _)]
    congr 1
    abel

end GlobalTheory.InertBigCell
