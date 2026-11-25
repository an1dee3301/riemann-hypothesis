module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.CoreSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Set.Operations
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

def EtaLt (r : Sym m n) (N : ℕ) : Prop := ∀ t ∈ r.support, (∑ k, t (Sum.inr k)) < N

def EtaLe (r : Sym m n) (N : ℕ) : Prop := ∀ t ∈ r.support, (∑ k, t (Sum.inr k)) ≤ N

def vecVar (ε : Fin m → Bool) (a : Fin m) (i : Fin n) : Sym m n :=
  if ε a then X (Sum.inl (a, i, false)) else X (Sum.inr (a, i, true))

def covVar (ε : Fin m → Bool) (b : Fin m) (i : Fin n) : Sym m n :=
  if ε b then X (Sum.inr (b, i, false)) else X (Sum.inl (b, i, true))

def pairSym (ε : Fin m → Bool) (a b : Fin m) : Sym m n := ∑ i, vecVar ε a i * covVar ε b i

def CompSt : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (u v : Sym m n) (d₁ d₂ : ℕ), SymbolInFirstFamily ε u → SymbolInFirstFamily ε v → EtaLe u d₁ → EtaLe v d₂ →
    ∃ r : Sym m n, SymbolInFirstFamily ε r ∧ EtaLt r (d₁ + d₂) ∧ ∀ f, op u (op v f) = op (u * v) f + op r f

def FFTSym : Prop :=
  PositivityTheory.Rg.Sw.FFT → ∀ (m n : ℕ) (ε : Fin m → Bool) (s : Sym m n), SymbolInFirstFamily ε s → (∀ i j, symK ε i j s = 0) →
    s ∈ Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m => (pairSym (n := n) ε ab.1 ab.2))

end PositivityTheory.Rg.Sw.LC
