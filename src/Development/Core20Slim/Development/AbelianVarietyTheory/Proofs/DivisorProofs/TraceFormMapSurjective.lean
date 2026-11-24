module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField

noncomputable section

namespace GlobalTheory.TraceDual

def traceFormMap (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] Module.Dual ℝ (κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.mk₂ ℝ (fun Y X => -(2 * Real.pi) *
      ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X i * Y i))
    (fun Y₁ Y₂ X => by simp [mul_add, Finset.sum_add_distrib]; ring)
    (fun c Y X => by simp [Finset.mul_sum, mul_left_comm])
    (fun Y X₁ X₂ => by simp [add_mul, Finset.sum_add_distrib, mul_add]; ring)
    (fun c Y X => by simp [Finset.mul_sum, mul_left_comm])

theorem traceFormMap_apply (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (Y X : κ → mixedEmbedding.mixedSpace F) :
    traceFormMap F κ Y X = -(2 * Real.pi) *
      ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X i * Y i) := rfl

theorem traceFormMap_injective (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Function.Injective (traceFormMap F κ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Y hY
  have h0 := LinearMap.congr_fun hY (fun i => GlobalTheory.VacLn.TrNondeg.conjM (Y i))
  rw [traceFormMap_apply, LinearMap.zero_apply] at h0
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have h1 : ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (GlobalTheory.VacLn.TrNondeg.conjM (Y i) * Y i) = 0 := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (neg_eq_zero.1 h) hpi
    · exact h
  have hnn : ∀ i, 0 ≤ Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (GlobalTheory.VacLn.TrNondeg.conjM (Y i) * Y i) := by
    intro i
    rw [GlobalTheory.VacLn.TrNondeg.trace_conjM_mul]
    exact add_nonneg (Finset.sum_nonneg fun w _ => sq_nonneg _)
      (Finset.sum_nonneg fun w _ => mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
  have e := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 h1
  funext i
  exact GlobalTheory.VacLn.TrNondeg.eq_zero_of_trace_conjM_mul _ (e i (Finset.mem_univ _))

theorem traceFormMap_surjective (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Function.Surjective (traceFormMap F κ) := by
  have h := Subspace.dual_finrank_eq (K := ℝ) (V := κ → mixedEmbedding.mixedSpace F)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h.symm).1
    (traceFormMap_injective F κ)

theorem exists_trace_rep : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ), ∃ Y : κ → mixedEmbedding.mixedSpace F,
      ∀ X, L X = -(2 * Real.pi) * ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X i * Y i) := by
  intro F _ _ κ _ L
  obtain ⟨Y, hY⟩ := traceFormMap_surjective F κ L.toLinearMap
  exact ⟨Y, fun X => by rw [← traceFormMap_apply, hY]; rfl⟩

end GlobalTheory.TraceDual
