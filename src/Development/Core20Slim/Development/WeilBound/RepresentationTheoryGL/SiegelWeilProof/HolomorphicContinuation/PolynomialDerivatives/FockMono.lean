module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Data.Cast
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
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
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def cr (c : ℝ) (k : Fin m × Fin n × Bool) : Module.End ℂ (PX m n) :=
  if k.2.2 then -((pderiv (R := ℂ) k).toLinearMap : Module.End ℂ (PX m n)) + (2 * c : ℂ) • LinearMap.mulLeft ℂ (X (k.1, k.2.1, false) : PX m n)
  else -((pderiv (R := ℂ) k).toLinearMap : Module.End ℂ (PX m n)) + (2 * c : ℂ) • LinearMap.mulLeft ℂ (X (k.1, k.2.1, true) : PX m n)

def fockMono (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : PX m n :=
  (((Finset.univ : Finset (Fin m × Fin n × Bool)).toList.map fun k => (cr c k) ^ (s k)).prod) 1

def fock (c : ℝ) (p : PX m n) : PX m n := ∑ s ∈ p.support, p.coeff s • fockMono c s

def Dop (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (p : PX m n) : PX m n :=
  if ε a = ε b then
    ∑ i, (X (b, i, true) * pderiv (a, i, true) p - X (a, i, false) * pderiv (b, i, false) p)
  else
    ∑ i, ((2 * c : ℂ) • pderiv (b, i, false) (pderiv (a, i, true) p) - (1 / (2 * c) : ℂ) • (X (a, i, false) * X (b, i, true) * p))

def contr (c : ℝ) (p : PX m n) : ℂ :=
  ∑ s ∈ p.support, if ∀ a i, s (a, i, false) = s (a, i, true) then
    p.coeff s * ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false))) else 0

def KopL (ε : Fin m → Bool) (i j : Fin n) : Module.End ℂ (PX m n) :=
  ∑ a ∈ Finset.univ.filter (fun a => ε a = true), LinearMap.mulLeft ℂ (X (a, i, false) : PX m n) ∘ₗ (pderiv (R := ℂ) (a, j, false)).toLinearMap -
    ∑ a ∈ Finset.univ.filter (fun a => ε a = false), LinearMap.mulLeft ℂ (X (a, j, true) : PX m n) ∘ₗ (pderiv (R := ℂ) (a, i, true)).toLinearMap

def mulQ (ε : Fin m → Bool) (i j : Fin n) (P : PX m n) : PX m n := Qp ε i j * P

def lapS (ε : Fin m → Bool) (c : ℝ) (i j : Fin n) (P : PX m n) : PX m n :=
  ∑ a, C (sgn ε a) * (pderiv (a, i, false) (pderiv (a, j, true) P - C (c : ℂ) * X (a, j, false) * P) -
    C (c : ℂ) * X (a, i, true) * (pderiv (a, j, true) P - C (c : ℂ) * X (a, j, false) * P))

def eulH (c : ℝ) (i j : Fin n) (P : PX m n) : PX m n :=
  ∑ a, X (a, j, false) * (pderiv (a, i, false) P - C (c : ℂ) * X (a, i, true) * P)

def eulA (c : ℝ) (i j : Fin n) (P : PX m n) : PX m n :=
  ∑ a, X (a, i, true) * (pderiv (a, j, true) P - C (c : ℂ) * X (a, j, false) * P)

def kAlg (ε : Fin m → Bool) : Subalgebra ℂ (Module.End ℂ (PX m n)) :=
  Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => KopL ε ij.1 ij.2)

end PositivityTheory.Rg.Sw.LC
