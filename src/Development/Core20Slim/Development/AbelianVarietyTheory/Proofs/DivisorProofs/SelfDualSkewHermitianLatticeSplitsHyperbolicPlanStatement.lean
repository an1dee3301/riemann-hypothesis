module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewHermitianLatticeSplitsHyperbolicPlan
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLowLat
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Trace.Defs

@[expose] public section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualSkewHermitianLattice_splits_hyperbolicPlane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ (n₁ : ℕ) (J : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E)
    (L : Submodule (𝓞 E) (Fin (n₁ + 2) → E)), (∀ i j, σ (J j i) = -J i j) → L.IsLattice E →
    (∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x))) →
    ∀ x : Fin (n₁ + 2) → E, x ≠ 0 → form σ J x x = 0 →
    ∃ (y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E), form σ J x y = 1 ∧ form σ J y y = 0 ∧
      (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      (∀ (s t : E) (u : Fin n₁ → E), s • x + ι *ᵥ u + t • y = 0 → s = 0 ∧ t = 0 ∧ u = 0) ∧
      ∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y := by
  first | exact @GlobalTheory.PlaneSkewSplit.split_global | exact GlobalTheory.PlaneSkewSplit.split_global | (intros; apply GlobalTheory.PlaneSkewSplit.split_global <;> assumption)
