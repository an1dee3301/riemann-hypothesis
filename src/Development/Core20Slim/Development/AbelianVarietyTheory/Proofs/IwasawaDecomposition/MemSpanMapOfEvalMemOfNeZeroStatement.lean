module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanMapOfEvalMemOfNeZero
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_map_of_eval_mem_of_ne_zero : ∀ (k : Type) [Field k] [Infinite k] (σ τ : Type) (M : Submodule k (MvPolynomial σ k)) (D : MvPolynomial τ k), D ≠ 0 → ∀ P : MvPolynomial σ (MvPolynomial τ k), (∀ y : τ → k, MvPolynomial.eval y D ≠ 0 → MvPolynomial.map (MvPolynomial.eval y) P ∈ M) → P ∈ Submodule.span (MvPolynomial τ k) (MvPolynomial.map (algebraMap k (MvPolynomial τ k)) '' (M : Set (MvPolynomial σ k))) := by
  first | exact @GlobalTheory.mem_span_map_of_eval_mem | exact GlobalTheory.mem_span_map_of_eval_mem | (intros; apply GlobalTheory.mem_span_map_of_eval_mem <;> assumption)
