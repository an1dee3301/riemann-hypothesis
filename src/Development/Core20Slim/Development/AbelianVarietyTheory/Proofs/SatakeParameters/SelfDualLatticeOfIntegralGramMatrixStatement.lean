module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualLatticeOfIntegralGramMatrix
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lattice_of_integral_gramMatrix : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
      (∀ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweG.HomA σ JS JT x y ↔
        ∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
      (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
        ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔
          ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) ∧
      (∀ w : Fin n → L, (∃ u v : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, v i ∈ Formalism.UG.intL L) ∧
          w = (a : Matrix (Fin n) (Fin n) L) *ᵥ u + v) ↔
        ∃ v : Fin n → L, ∃ w' : Fin n' → L, (∀ i, v i ∈ Formalism.UG.intL L) ∧ (∀ i, w' i ∈ Formalism.UG.intL L) ∧
          w = v + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') := by
  first | exact @GlobalTheory.Hk3.HoweG.selfDual_lattice_of_gram_int | exact GlobalTheory.Hk3.HoweG.selfDual_lattice_of_gram_int | (intros; apply GlobalTheory.Hk3.HoweG.selfDual_lattice_of_gram_int <;> assumption)
