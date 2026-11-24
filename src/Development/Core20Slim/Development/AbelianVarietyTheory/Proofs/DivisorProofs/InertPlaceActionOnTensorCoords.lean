module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InclRMulPtAt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

namespace GlobalTheory.InertCoordAct

theorem at_mul_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : At (evFin F v) z) : At (evFin F v) (a * z) := fun u hu => by
  rw [← mul_smul_comm, hz u hu, mul_zero]

theorem at_mul_right {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : At (evFin F v) z) : At (evFin F v) (z * a) := fun u hu => by
  rw [← smul_mul_assoc, hz u hu, zero_mul]

theorem at_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    {ι : Type} (s : Finset ι) (f : ι → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hf : ∀ i, At (evFin F v) (f i)) :
    At (evFin F v) (∑ i ∈ s, f i) := fun u hu => by
  rw [Finset.smul_sum]; exact Finset.sum_eq_zero fun i _ => hf i u hu

theorem act_kap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E))
    (g₁ : UA σ X.J) (g₂ : UA σ Y.J), g₁ ∈ UAt σ X (evFin F v) → g₂ ∈ UAt σ Y (evFin F v) → ∀ x,
      actAB (cA σ) (g₁, g₂) (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) =
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))
          ((((Bm⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) * (mat g₂).map (locW h) *
              (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))) * x *
            (((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (mat g₁).map (locW h) *
              (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ) := by
  intro F E _ _ _ _ _ σ v w hw h n d X Y A Bm g₁ g₂ _ _ x
  set P : Matrix (Fin n) (Fin d) (w.adicCompletion E) := (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * xᵀ * (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ with hP
  have hK : kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x = P.map (ptAt hw h) := kap_apply hw h _ _ x
  have hmm : (P.map (ptAt hw h)).map (locW h) = P := by
    rw [Matrix.map_map]; exact Matrix.ext fun i j => locW_ptAt hw h _
  rw [hK, kap_apply]
  simp only [actAB]
  change mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ = _
  have hat : ∀ i j, At (evFin F v) ((mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ) i j) := fun i j => by
    simp only [Matrix.mul_apply]
    refine at_sum _ _ fun k => at_mul_right _ (at_sum _ _ fun l => at_mul_left _ (at_ptAt hw h _))
  have e1 : mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ =
      ((mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ).map (locW h)).map (ptAt hw h) := by
    exact Matrix.ext fun i j => (ptAt_locW hw h (hat i j)).symm
  rw [e1]
  congr 1
  rw [Matrix.map_mul, Matrix.map_mul, hmm, Matrix.transpose_map, hP]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hB : (((Bm⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)))ᵀ *
      ((Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
  have hA : (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * ((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hB, Matrix.mul_one, ← Matrix.mul_assoc (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)), hA, Matrix.one_mul]

end GlobalTheory.InertCoordAct
