module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassElementaryDivisorColumnsCongr
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramClass_elementaryDivisor_columns_congr : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L)
    (V : Matrix (Fin n) (Fin n) L) (a : Fin n → ℕ), (∀ i j, V i j ∈ Formalism.UG.intL L) →
    (∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (x *ᵥ (V *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j))) →
    GlobalTheory.Hk3.HoweG.GramEq σ JT x y →
    ∀ i j : Fin n, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (min (a i) (a j))
      (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (y *ᵥ (V *ᵥ Pi.single i (ϖ ^ a i))) (y *ᵥ (V *ᵥ Pi.single j (ϖ ^ a j))) -
        Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (x *ᵥ (V *ᵥ Pi.single i (ϖ ^ a i))) (x *ᵥ (V *ᵥ Pi.single j (ϖ ^ a j)))) := by
  first | exact @GlobalTheory.Hk3.IntWitt.gram_class_columns | exact GlobalTheory.Hk3.IntWitt.gram_class_columns | (intros; apply GlobalTheory.Hk3.IntWitt.gram_class_columns <;> assumption)
