module

public import Mathlib
public import Formalism.PairingDivisors.PairingDivisorProofs.ValAdd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.ProdFormula
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Formalism.GradedWeylDivisibility.StatementD
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.QuotientMetricDivisors.Statement
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

section

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def nonnegRing_vw (w : HeightOneSpectrum (𝓞 K)) : Subring K where
  carrier := {a | 0 ≤ vw w a}
  zero_mem' := (ValuationRepresentative.vw_zero w).ge
  one_mem' := (ValuationRepresentative.vw_one w).ge
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    by_cases h0 : a = 0
    · rw [h0, zero_mul]; exact (ValuationRepresentative.vw_zero w).ge
    by_cases h1 : b = 0
    · rw [h1, mul_zero]; exact (ValuationRepresentative.vw_zero w).ge
    rw [ValuationRepresentative.vw_mul w a b h0 h1]
    exact add_nonneg ha hb
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    by_cases h0 : a = 0
    · rwa [h0, zero_add]
    by_cases h1 : b = 0
    · rwa [h1, add_zero]
    by_cases h2 : a + b = 0
    · rw [h2]; exact (ValuationRepresentative.vw_zero w).ge
    exact (le_min ha hb).trans (Formalism.PairingDivisionLocalBalance.vw_add w a b h0 h1 h2)
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    by_cases h0 : a = 0
    · rw [h0, neg_zero]; exact (ValuationRepresentative.vw_zero w).ge
    have h1 : 0 ≤ vw w (-1 : K) := by
      have := ValuationRepresentative.vw_int_nonneg w (-1 : 𝓞 K)
      simpa using this
    rw [← neg_one_mul, ValuationRepresentative.vw_mul w _ a (neg_ne_zero.2 one_ne_zero) h0]
    exact add_nonneg h1 ha

end

section

variable {K : Type} [Field K] (R : Subring K)

theorem mem_range_map_subtype_iff {σ : Type} (P : MvPolynomial σ K) :
    P ∈ (MvPolynomial.map (σ := σ) R.subtype).range ↔ ∀ m, AddMonoidAlgebra.coeff P m ∈ R := by
  constructor
  · rintro ⟨Q, rfl⟩ m
    rw [coeff_map]
    exact (AddMonoidAlgebra.coeff Q m).2
  · intro h
    rw [P.as_sum]
    exact sum_mem fun m _ => ⟨monomial m ⟨_, h m⟩, by rw [map_monomial]; rfl⟩

theorem blockAct_mem_range_map_subtype {ι : Type} [Fintype ι] {n : ℕ}
    (U : ι → Matrix (Fin n) (Fin n) K) (hU : ∀ τ a b, U τ a b ∈ R)
    {P : MvPolynomial (ι × Fin n × Fin n) K}
    (hP : P ∈ (MvPolynomial.map (σ := ι × Fin n × Fin n) R.subtype).range) :
    Formalism.GradedWeylDivisibility.blockAct K U P ∈ (MvPolynomial.map (σ := ι × Fin n × Fin n) R.subtype).range := by
  have hC : ∀ {a : K}, a ∈ R → (C a : MvPolynomial (ι × Fin n × Fin n) K) ∈
      (MvPolynomial.map (σ := ι × Fin n × Fin n) R.subtype).range :=
    fun {a} ha => ⟨C ⟨a, ha⟩, by simp⟩
  have hX : ∀ v, (X v : MvPolynomial (ι × Fin n × Fin n) K) ∈
      (MvPolynomial.map (σ := ι × Fin n × Fin n) R.subtype).range :=
    fun v => ⟨X v, by simp⟩
  obtain ⟨Q, rfl⟩ := hP
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [map_C, algHom_C]
    exact hC a.2
  | add p q hp hq =>
    rw [map_add (MvPolynomial.map R.subtype), map_add (f := _)]
    exact add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul (MvPolynomial.map R.subtype), map_X, map_mul, blockAct_X]
    exact mul_mem hp (sum_mem fun b _ => mul_mem (hC (hU _ _ _)) (hX _))

end

theorem vw_fockS_blockAct_nonneg : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (w : HeightOneSpectrum (𝓞 K)) (F F' : Pol K ι n) (U : ι → Matrix (Fin n) (Fin n) K), (∀ mo, 0 ≤ vw (conjPl w) (AddMonoidAlgebra.coeff F mo)) → (∀ mo, 0 ≤ vw w (AddMonoidAlgebra.coeff F' mo)) → (∀ τ a b, 0 ≤ vw w (U τ a b)) → 0 ≤ vw w (fockS F (Formalism.GradedWeylDivisibility.blockAct K U F')) := by
  intro K _ _ _ ι _ n w F F' U hF hF' hU
  have h := (mem_range_map_subtype_iff (nonnegRing_vw w) _).1
    (blockAct_mem_range_map_subtype (nonnegRing_vw w) U hU
      ((mem_range_map_subtype_iff (nonnegRing_vw w) F').2 hF'))
  change fockS F (Formalism.GradedWeylDivisibility.blockAct K U F') ∈ nonnegRing_vw w
  unfold fockS
  refine sum_mem fun m _ => mul_mem (mul_mem ?_ (h m)) (natCast_mem _ _)
  change 0 ≤ vw w (star (AddMonoidAlgebra.coeff F m))
  rw [ValuationRepresentative.vw_star]
  exact hF m

end GlobalTheory.TestLat
