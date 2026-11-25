module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftDefs
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalRingCardinality.DataCoeff
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTBranch
public import Development.Core20Slim.Formalism.PeriodIntegrals.GTDefs
public import Init.Core
public import Init.Data.Cast
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

noncomputable section

namespace PI.WGL.LTM

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

def liftRows {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) : Fin (m + 1) → Fin N :=
  fun p => if hp : p.1 < m then eRow h (ρ ⟨p.1, hp⟩) else ⟨N - 1, by omega⟩

def unl {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m ≤ N) :
    MvPolynomial (Fin N × Fin N) ℤ :=
  initMinor ℤ (eRow h ∘ ρ) hm

def lif {n N : ℕ} (h : n + 1 = N) {m : ℕ} (ρ : Fin m → Fin n) (hm : m + 1 ≤ N) :
    MvPolynomial (Fin N × Fin N) ℤ :=
  initMinor ℤ (liftRows h ρ) hm

def C0 {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : MvPolynomial (Fin N × Fin N) ℤ :=
  ∏ i : Fin n, (if i.1 + 1 = n then (lpMinor ℤ (r := N) (n := N) (i.1 + 1) (by omega) (by omega)) ^ (aa h lam sg i).toNat
      else 1) *
    (if i.1 = 0 then (initMinor ℤ (n := N) (rowsZ h i) (by omega)) ^ (bb h lam sg i).toNat else 1)

def Mlift {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K)) (I : ∀ k, Fin (sz k) → Fin n) : MvPolynomial (Fin N × Fin N) ℤ :=
  C0 h lam sg * ∏ k : Fin K,
    if k ∈ L then lif h (I k) (by have := hsz k; omega) else unl h (I k) (by have := hsz k; omega)

def GoodL {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (L : Finset (Fin K)) : Prop :=
  (∀ k ∈ L, 0 < sz k) ∧
  ∀ i : Fin n, (Finset.univ.filter fun k => k ∈ L ∧ sz k = i.1).card = if i.1 = 0 then 0 else (bb h lam sg i).toNat

def stdT {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) : ∀ k, Fin (sz k) → Fin n :=
  fun k p => ⟨p.1, lt_of_lt_of_le p.2 (hsz k)⟩

def TopPart : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg →
    ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n), shapeDeg sz = sg.natW →
    ∀ L : Finset (Fin K), GoodL h lam sg sz L →
      (∀ J, tupCnt J = sg.natW →
        ∃ ε : ℤ, bideterminant ℤ sz hsz J = ε • extremal ℤ n sg ∧ Mlift h lam sg sz hsz L J = ε • xi ℤ h lam sg) ∧
      tupCnt (stdT sz hsz) = sg.natW ∧ bideterminant ℤ sz hsz (stdT sz hsz) = extremal ℤ n sg ∧
        Mlift h lam sg sz hsz L (stdT sz hsz) = xi ℤ h lam sg

end PI.WGL.LTM
