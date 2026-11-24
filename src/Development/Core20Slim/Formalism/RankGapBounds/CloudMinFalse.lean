module

public import Mathlib
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Nat

@[expose] public section

namespace Formalism.RankGapBounds.JumpSetsAlt

open Finset

def maxVal (l n : ℕ) : ℕ := (Finset.range (n + 1)).sup fun i => (Nat.choose n i).factorization l

def posPairs (N : ℕ) : Finset (Fin N × Fin N) := Finset.univ.filter fun p => p.1 < p.2

def eExp {N : ℕ} (U : Fin N → ℤ) (l : ℕ) : ℕ :=
  ∑ p ∈ posPairs N, maxVal l (U p.1 - U p.2 - 1).toNat

end Formalism.RankGapBounds.JumpSetsAlt
