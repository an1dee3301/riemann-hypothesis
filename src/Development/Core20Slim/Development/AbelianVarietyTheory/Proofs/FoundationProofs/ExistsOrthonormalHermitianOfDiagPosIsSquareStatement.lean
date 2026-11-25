module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrthonormalHermitianOfDiagPosIsSquare
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandherrAndLandherrSt
public import Batteries.Classes.RatCast
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_hermitian_of_diag_pos_isSquare : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (d : ℕ) (θ : K), 0 < d → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → ∀ (r : ℕ) (v : Fin r → V) (a : Fin r → ℚ), (∀ i, 0 < a i) → (∀ i j, h (v i) (v j) = if i = j then (a i : K) else 0) → IsSquare (∏ i, a i) → ∃ e : Fin r → V, ∀ i j, h (e i) (e j) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.SqDet.exists_orthonormal_of_diag_pos_isSquare | exact GlobalTheory.SqDet.exists_orthonormal_of_diag_pos_isSquare | (intros; apply GlobalTheory.SqDet.exists_orthonormal_of_diag_pos_isSquare <;> assumption)
