module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GlobalTheory.CoefficientSpanFiniteDimensional

theorem dual_apply_eq_sum {W ι : Type} [AddCommGroup W] [Module ℂ W] [Fintype ι] (b : Module.Basis ι ℂ W)
    (ℓ : Module.Dual ℂ W) (w : W) (A : W →ₗ[ℂ] W) :
    ℓ (A w) = ∑ j, ∑ i, (b.repr w j * ℓ (b i)) * b.repr (A (b j)) i := by
  conv_lhs => rw [← b.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul]
  conv_lhs => rw [← b.sum_repr (A (b j))]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ ↥(GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  classical
  let b := Module.finBasis ℂ W
  let e : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W) → (K → ℂ) :=
    fun p k => b.repr (ρ k (b p.2)) p.1
  haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range e)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range e)) (Submodule.span_le.mpr ?_)
  rintro f ⟨ℓ, w, rfl⟩
  have h : (fun k => ℓ (ρ k w)) = ∑ j, ∑ i, (b.repr w j * ℓ (b i)) • e (i, j) := by
    funext k
    rw [dual_apply_eq_sum b ℓ w (ρ k)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e]
  rw [h]
  exact Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)

end GlobalTheory.CoefficientSpanFiniteDimensional
