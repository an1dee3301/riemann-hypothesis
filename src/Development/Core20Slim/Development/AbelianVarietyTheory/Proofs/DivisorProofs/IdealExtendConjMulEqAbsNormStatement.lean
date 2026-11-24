module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealExtendConjMulEqAbsNorm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealExtend_conj_mul_eq_absNorm : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)), (∀ α ∈ GlobalTheory.VacRead.cE D cc, ∀ β ∈ GlobalTheory.VacRead.cE D cc, ∃ o : 𝓞 D.host.E, D.host.conj α * β = (Ideal.absNorm cc : D.host.E) * (o : D.host.E)) ∧ (Ideal.absNorm cc : D.host.E) ∈ Submodule.span (𝓞 D.host.E) {t | ∃ α ∈ GlobalTheory.VacRead.cE D cc, ∃ β ∈ GlobalTheory.VacRead.cE D cc, t = D.host.conj α * β} := by
  first | exact @GlobalTheory.VacRead.conj_mul_cE_absNorm | exact GlobalTheory.VacRead.conj_mul_cE_absNorm | (intros; apply GlobalTheory.VacRead.conj_mul_cE_absNorm <;> assumption)
