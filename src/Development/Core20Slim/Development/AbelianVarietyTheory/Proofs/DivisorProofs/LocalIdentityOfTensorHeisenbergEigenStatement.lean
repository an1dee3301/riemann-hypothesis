module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdentityOfTensorHeisenbergEigen
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromColsMemLatDbl
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localIdentity_of_tensorHeisenbergEigen : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (γ : W) (f : (κ → Fv F v) → ℂ)
    (R : (κ → AF F) → ℂ) (c : ℂ), At (evFin F v) γ → (∀ x z, At (evFin F v) z → R (x + z) = R x) →
    ∀ x₀, R x₀ ≠ 0 → co.rho ψ γ (tens (evFin F v) f R) = c • tens (evFin F v) f R →
    ∀ ξ : κ → Fv F v, GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2)) *
      f (ξ + (GlobalTheory.LatVac.locCo co v γ).1) = c * f ξ := by
  first | exact @GlobalTheory.DblVacEigen.local_identity_of_tens_eigen | exact GlobalTheory.DblVacEigen.local_identity_of_tens_eigen | (intros; apply GlobalTheory.DblVacEigen.local_identity_of_tens_eigen <;> assumption)
