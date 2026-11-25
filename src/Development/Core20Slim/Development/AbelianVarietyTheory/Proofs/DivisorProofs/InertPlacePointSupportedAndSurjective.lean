module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InclRMulPtAt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
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

namespace GlobalTheory.InertCoord

theorem kap_at_and_onto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {m n : ℕ}
    (A : GL (Fin m) (w.adicCompletion E)) (Bm : GL (Fin n) (w.adicCompletion E)),
    (∀ x, At (evFin F v) (kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x)) ∧
    ∀ γ : Matrix (Fin m) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) γ →
      ∃ x, kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x = γ := by
  intro F E _ _ _ _ _ v w hw h m n A Bm
  refine ⟨fun x u hu => ?_, fun γ hγ => ?_⟩
  · ext i j
    rw [Matrix.smul_apply, kap_apply, Matrix.map_apply, Matrix.zero_apply]
    exact at_ptAt hw h _ u hu
  · refine ⟨(((A⁻¹ : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) * γ.map (locW h) *
        ((((Bm⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ))ᵀ, ?_⟩
    rw [kap_apply, Matrix.transpose_transpose]
    have e : (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *
        (((A⁻¹ : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) * γ.map (locW h) *
        ((((Bm⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ)) *
        (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ = γ.map (locW h) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mul]
    rw [e]
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply]
    refine ptAt_locW hw h fun u hu => ?_
    have := congrFun (congrFun (hγ u hu) i) j
    rwa [Matrix.smul_apply, Matrix.zero_apply] at this

end GlobalTheory.InertCoord
