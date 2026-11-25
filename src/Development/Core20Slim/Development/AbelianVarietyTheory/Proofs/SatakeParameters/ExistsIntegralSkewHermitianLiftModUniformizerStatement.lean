module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralSkewHermitianLiftModUniformizer
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformTrivialPhaseSkewHermitian
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_skew_hermitian_lift_mod_uniformizer : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (z w a : ι → Fin n' → L),
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, w i r ∈ Formalism.UG.intL L) → (∀ i r, a i r ∈ Formalism.UG.intL L) →
    (∀ i j, ∑ r, a i r * z j r = if i = j then 1 else 0) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (w j) +
      Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (w i) (z j))) →
    ∃ C : Matrix (Fin n') (Fin n') L, (∀ r s, σ (C r s) = - C s r) ∧ (∀ r s, C r s ∈ Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((C *ᵥ z i) r - ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w i) r) := by
  first | exact @GlobalTheory.Hk3.SkewLift.skew_lift | exact GlobalTheory.Hk3.SkewLift.skew_lift | (intros; apply GlobalTheory.Hk3.SkewLift.skew_lift <;> assumption)
