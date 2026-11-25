module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.ThetaLifts.Reductions.SiegelPar
public import Development.Core20Slim.GroundTheory.AutomorphicForms.ReductionHeight
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Function
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Topology.Defs.Filter

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}


variable (F) in
def ratV (z : Fin n → E) : Fin n → AF F ⊗[F] E := fun i => inclR (F := F) (AF F) (z i)

def hv (ξ : Fin n → AF F ⊗[F] E) : ℝ :=
  GroundTheory.Automorphic.Reduction.adelicNorm
    (fun p : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) =>
      (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).repr
        (ξ ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).1)
        ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).2)

def hgt (g : GAd σ J) (v : Fin n → E) : ℝ := hv ((matHom _ σ J g⁻¹).1 *ᵥ ratV F v)

def Sends (γ : GAd σ J) (u v : Fin n → E) : Prop := (matHom _ σ J γ).1 *ᵥ ratV F u = ratV F v

def NearMin (g : GAd σ J) (v : Fin n → E) : Prop :=
  v ≠ 0 ∧ hE σ J v v = 0 ∧ ∀ u : Fin n → E, u ≠ 0 → hE σ J u u = 0 → hgt σ J g v ≤ 2 * hgt σ J g u

def HasRed (X Y : Matrix (Fin n) (Fin r) E) : Prop :=
  ∀ a, IsTorus σ J X Y a → ∃ (C : Set (GAd σ J)) (c : ℝ), IsCompact C ∧ 0 < c ∧
    ∀ g, ∃ γ ∈ ratPts σ J, ∃ q ∈ minParOne σ J X, ∃ s : Fin r → ℝ,
      (fun i => Real.exp (s i)) ∈ cone r c ∧ ∃ κ ∈ C, g = γ * q * a s * κ

theorem ratV_injective : Function.Injective (ratV F : (Fin n → E) → Fin n → AF F ⊗[F] E) := by
  intro u v h
  funext i
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  haveI : Nontrivial (AF F) := (evInf F w : AF F →+* w.Completion).domain_nontrivial
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective (congrFun h i)

variable {σ J}

theorem Sends.inv {γ : GAd σ J} {u v : Fin n → E} (h : Sends σ J γ u v) : Sends σ J γ⁻¹ v u := by
  unfold Sends at h ⊢
  rw [← h, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]

theorem hgt_mul {γ g : GAd σ J} {u v : Fin n → E} (h : Sends σ J γ⁻¹ v u) : hgt σ J (γ⁻¹ * g) u = hgt σ J g v := by
  unfold Sends at h
  unfold hgt
  rw [← h, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
  simp [_root_.mul_inv_rev]

end GlobalTheory.CompanionTheory.RedCov

end
