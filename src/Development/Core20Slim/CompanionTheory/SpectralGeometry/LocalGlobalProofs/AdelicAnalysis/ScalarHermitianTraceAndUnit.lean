module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.ScalTrace

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem hermScal_entry {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (R : Type) [CommRing R] [Algebra F R] (s : R) :
    (hermScal R σ s : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 = algebraMap R (R ⊗[F] E) s := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem trace_det : ∀ (F E : Type) [Field F] [Field E] [Algebra F E], (1 / 2 : F) ≠ 0 → Module.finrank F E = 2 → ∀ (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (β : F), algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((hermScal R σ (algebraMap F R β) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) = algebraMap F R β ∧ (β ≠ 0 → IsUnit ((hermScal R σ (algebraMap F R β) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))).det) := by
  intro F E _ _ _ h2 hf σ R _ _ β
  have hfin : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hf
  have hent := hermScal_entry σ R (algebraMap F R β)
  refine ⟨?_, fun hβ => ?_⟩
  · rw [hent, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b) (algebraMap F R β)]
    have h20 : (2 : F) ≠ 0 := by
      intro h
      apply h2
      simp [h]
    have hhalf : algebraMap F R (1 / 2) * algebraMap F R 2 = 1 := by
      rw [← map_mul, one_div, inv_mul_cancel₀ h20, map_one]
    rw [Fintype.card_fin, nsmul_eq_mul]
    have h2R : ((2 : ℕ) : R) = algebraMap F R 2 := by
      rw [map_ofNat]
      norm_num
    rw [h2R, ← mul_assoc, hhalf, one_mul]
  · rw [Matrix.det_fin_one, hent]
    exact ((isUnit_iff_ne_zero.2 hβ).map (algebraMap F R)).map (algebraMap R (R ⊗[F] E))

end GlobalTheory.CompanionTheory.SW.BB.ScalTrace
