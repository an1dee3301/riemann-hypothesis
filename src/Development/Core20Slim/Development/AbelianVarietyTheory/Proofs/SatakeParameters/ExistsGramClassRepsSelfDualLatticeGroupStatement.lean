module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGramClassRepsSelfDualLatticeGroup
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementF
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gramClass_reps_selfDualLattice_group : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    (Valued.v δ = 1 ∧ σ δ = -δ) → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
      (∀ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweG.HomA σ JS JT x y ↔
        ∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
      (∀ v : Fin n → L, (∀ i, v i ∈ Formalism.UG.intL L) →
        ((∃ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ u) ↔
          ∀ i, (x *ᵥ v) i ∈ Formalism.UG.intL L)) ∧
      (∀ w : Fin n → L, (∃ u v : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, v i ∈ Formalism.UG.intL L) ∧
          w = (a : Matrix (Fin n) (Fin n) L) *ᵥ u + v) ↔
        ∃ v : Fin n → L, ∃ w' : Fin n' → L, (∀ i, v i ∈ Formalism.UG.intL L) ∧ (∀ i, w' i ∈ Formalism.UG.intL L) ∧
          w = v + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') →
    ∃ Y : Finset (Matrix (Fin n') (Fin n) L), x ∈ Y ∧ (∀ y ∈ Y, GlobalTheory.Hk3.HoweG.HomA σ JS JT x y) ∧
      (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n → y = y') ∧
      ∃ (B : Type) (_ : AddCommGroup B) (_ : Fintype B) (b0 : B → GL (Fin n) L)
        (l : B → Matrix (Fin n') (Fin n) L → Matrix (Fin n') (Fin n) L),
        (∀ b, GlobalTheory.Hk3.HoweG.SelfDual σ JS (b0 b)) ∧
        (∀ b, ∀ y ∈ Y, l b y ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n ∧
          ∃ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
            y + l b y = u * (((b0 b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ∧
        (∀ b, ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
          ∃ y ∈ Y, u * (((b0 b)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - (y + l b y) ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n) ∧
        (∀ b b', ∀ y ∈ Y, ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l (b + b') y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l (b + b') y))) / 2)) = ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l b y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l b y))) / 2)) * ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l b' y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l b' y))) / 2))) ∧
        (∀ y ∈ Y, GlobalTheory.Hk3.HoweG.GramEq σ JT x y ↔ ∀ b, ψ (-((GlobalTheory.Hk3.locH σ δ JS JT y (l b y) + σ (GlobalTheory.Hk3.locH σ δ JS JT y (l b y))) / 2)) = ψ (-((GlobalTheory.Hk3.locH σ δ JS JT x (l b x) + σ (GlobalTheory.Hk3.locH σ δ JS JT x (l b x))) / 2))) := by
  first | exact @GlobalTheory.Hk3.GramSep.gram_class_family | exact GlobalTheory.Hk3.GramSep.gram_class_family | (intros; apply GlobalTheory.Hk3.GramSep.gram_class_family <;> assumption)
