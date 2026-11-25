module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum

variable {D : D7}

theorem mul_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {s x : AE D} (hs : s ∈ OhE D) (hx : x ∈ hatId D 𝔪) :
    s * x ∈ hatId D 𝔪 := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, t, ht, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, s * t, mul_mem hs ht, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg _ _ h => rw [mul_neg]; exact neg_mem h

theorem mem_hatId_mul {𝔪 : Ideal (𝓞 D.host.E)} {s x : AE D} (hs : s ∈ OhE D) (hx : x ∈ hatId D 𝔪) :
    x * s ∈ hatId D 𝔪 := by
  rw [mul_comm]; exact mul_mem_hatId hs hx

theorem congOne_mul {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {k k' : GA D N} (hk' : k' ∈ intG D N)
    (h : CongOne D 𝔪 k) (h' : CongOne D 𝔪 k') : CongOne D 𝔪 (k * k') := by
  intro i j
  have hi := (mem_intG k').1 hk'
  have e : (((k * k' : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1 =
      ((((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1) *
        ((k' : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) +
      ((((k' : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) - 1) := by
    simp only [Subgroup.coe_mul, Units.val_mul, sub_mul, one_mul]; abel
  rw [e, Matrix.add_apply, Matrix.mul_apply]
  exact add_mem (sum_mem fun l _ => mem_hatId_mul (hi l j).1 (h i l)) (h' i j)

theorem congOne_inv {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {k : GA D N} (hk : k ∈ intG D N)
    (h : CongOne D 𝔪 k) : CongOne D 𝔪 k⁻¹ := by
  intro i j
  have hi := (mem_intG k).1 hk
  have e : (((k⁻¹ : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1 =
      -((((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        ((((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) - 1)) := by
    rw [Subgroup.coe_inv, mul_sub, Units.inv_mul, mul_one, neg_sub]
  rw [e, Matrix.neg_apply, Matrix.mul_apply]
  exact neg_mem (sum_mem fun l _ => mul_mem_hatId (hi i l).2 (h l j))

theorem congOne_one (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) : CongOne D 𝔪 (1 : GA D N) := by
  intro i j
  simp only [OneMemClass.coe_one, Units.val_one, sub_self, Matrix.zero_apply]
  exact zero_mem _

theorem mem_congLev_iff : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) (k : GA D N),
    k ∈ congLev D 𝔪 N ↔ k ∈ intG D N ∧ CongOne D 𝔪 k := by
  intro D 𝔪 N k
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  induction h using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨one_mem _, congOne_one 𝔪 N⟩
  | mul x y _ _ hx hy => exact ⟨mul_mem hx.1 hy.1, congOne_mul hy.1 hx.2 hy.2⟩
  | inv x _ hx => exact ⟨inv_mem hx.1, congOne_inv hx.1 hx.2⟩

end GlobalTheory.FunObj.StdDatum

end
