module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FockMono
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

def FockBasic : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → IsLinearMap ℂ (fock (m := m) (n := n) c) ∧ Function.Bijective (fock (m := m) (n := n) c) ∧
    ∀ k (p : PX m n), fock c (X k * p) = cr c k (fock c p)

def FockHOp : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ (a b : Fin m) (p : PX m n),
    hOp ε c a b (fock c p) = fock c (Dop ε c a b p)

def FockMom : Prop :=
  ∀ (m n : ℕ) (c : ℝ), 0 < c → mom (m := m) (n := n) c 1 ≠ 0 ∧ ∀ p : PX m n, mom c (fock c p) = mom c (1 : PX m n) * contr c p

def NullStable : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ (i j : Fin n) (P : PX m n), NullSec ε c P →
    NullSec ε c (lapS ε c i j P) ∧ NullSec ε c (eulH c i j P) ∧ NullSec ε c (eulA c i j P) ∧ NullSec ε c (mulQ ε i j P)

def FockK : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∃ a₁ a₂ a₃ a₄ a₅ : ℂ, ∀ (i j : Fin n) (p : PX m n),
    fock c (KopL ε i j p) = a₁ • mulQ ε i j (fock c p) + a₂ • lapS ε c i j (fock c p) + a₃ • eulH c i j (fock c p) +
      a₄ • eulA c i j (fock c p) + (if i = j then a₅ else 0) • fock c p

def CoreLC : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c : ℝ), 0 < c → ∀ Λ : PX m n →ₗ[ℂ] ℂ, (∀ a b p, Λ (Dop ε c a b p) = 0) →
    ∀ p, ∃ w ∈ kAlg ε, Λ p = contr c (w p)

end PositivityTheory.Rg.Sw.LC
