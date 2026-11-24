module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
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
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.VacLift

theorem exists_lift_scalar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (a : Fv F v) :
    ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ piW (t.comp σ) z = 0 ∧ piW t z = a := by
  have hp : ∀ (s : E →ₐ[F] Fv F v) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), piW s z = splitProj s (compFin F E v z) := fun s z => rfl
  have hs : ∀ (s : E →ₐ[F] Fv F v) (u : AF F) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), piW s (u • z) = evFin F v u * piW s z := by
    intro s u z
    rw [Algebra.smul_def, map_mul]
    congr 1
    rw [hp]
    change splitProj s (TensorProduct.tmul F (evFin F v u) (1 : E)) = _
    rw [splitProj_tmul, map_one, mul_one]
  refine ⟨GlobalTheory.LatVac.liftV v a • Supp.splitIdemAd h t, ?_, ?_, ?_⟩
  · intro u hu
    rw [smul_smul, ← smul_eq_mul u, GlobalTheory.LatVac.at_liftV v a u hu, zero_smul]
  · rw [hs, hp, Supp.splitIdemAd, Supp.compFin_singleTens_self]
    simp [splitIdem]
  · rw [hs, hp, Supp.splitIdemAd, Supp.compFin_singleTens_self, GlobalTheory.LatVac.evFin_liftV]
    simp [splitIdem]

theorem exists_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) x ∧
      x.map (piW (t.comp σ)) = 0 ∧ (b⁻¹).1 * x.map (piW t) * (c⁻¹).1ᵀ = Y := by
  intro F E _ _ _ _ _ σ n d h v t b c Y
  choose f hf using exists_lift_scalar h v t
  refine ⟨(b.1 * Y * c.1ᵀ).map f, ?_, ?_, ?_⟩
  · intro u hu
    ext i j
    exact (hf _).1 u hu
  · exact Matrix.ext fun i j => (hf _).2.1
  · have e : ((b.1 * Y * c.1ᵀ).map f).map (piW t) = b.1 * Y * c.1ᵀ :=
      Matrix.ext fun i j => (hf _).2.2
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.mul_one]

end GlobalTheory.VacLift
