module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieSmoothAndLinear
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

noncomputable section

namespace GlobalTheory.CuspGeo.MeanValue

section Abstract

open GlobalTheory.SmoothForms

variable {L G ι : Type} [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] [Fintype ι]

theorem norm_sub_le (e : L → G) (he0 : e 0 = 1) (he : ∀ (Z : L) (s t : ℝ), e ((s + t) • Z) = e (s • Z) * e (t • Z))
    (b : Module.Basis ι ℝ L) {φ : G → ℂ} (hφ : Sm e φ) (g : G) (Z : L) (a : ℝ) (ha : ∀ i, |b.repr Z i| ≤ a) (c : ι → ℝ)
    (hc : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Der e (b i) φ (g * e (t • Z))‖ ≤ c i) :
    ‖φ (g * e Z) - φ g‖ ≤ a * ∑ i, c i := by
  have hc0 : ∀ i, 0 ≤ c i := fun i => (norm_nonneg _).trans (hc i 0 ⟨le_refl 0, zero_le_one⟩)

  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => φ (g * e (s • Z)))
      (fderiv ℝ (fun X : L => φ (g * e (t • Z) * e X)) ((t - t) • Z) Z) t := by
    intro t
    have hF : Differentiable ℝ (fun X : L => φ (g * e (t • Z) * e X)) :=
      (hφ (g * e (t • Z))).differentiable (by simp)
    have h1 : HasDerivAt (fun s : ℝ => (s - t) • Z) ((1 : ℝ) • Z) t :=
      ((hasDerivAt_id' t).sub_const t).smul_const Z
    rw [one_smul] at h1
    have h2 := (hF ((t - t) • Z)).hasFDerivAt.comp_hasDerivAt t h1
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show φ (g * e (s • Z)) = φ (g * e (t • Z) * e ((s - t) • Z))
    rw [mul_assoc, ← he, show t + (s - t) = s by ring]

  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fun X : L => φ (g * e (t • Z) * e X)) 0 Z‖ ≤ a * ∑ i, c i := by
    intro t ht
    set F' := fderiv ℝ (fun X : L => φ (g * e (t • Z) * e X)) 0 with hF'
    have hZ : F' Z = ∑ i, b.repr Z i • F' (b i) := by
      have : F' Z = F' (∑ i, b.repr Z i • b i) := by rw [b.sum_repr]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, map_sum]
      simp only [map_smul]
    rw [hZ, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    have hi : ‖F' (b i)‖ ≤ c i := by
      have := hc i t ht
      rwa [DerLinear.der_eq_fderiv hφ] at this
    exact mul_le_mul (ha i) hi (norm_nonneg _) ((abs_nonneg _).trans (ha i))
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => φ (g * e (s • Z))) (fun t _ => (hderiv t).hasDerivWithinAt)
    (fun t ht => by
      rw [sub_self, zero_smul]
      exact key t (Set.Ico_subset_Icc_self ht))
  simpa [he0] using hmv

theorem exists_coord_bound (b : Module.Basis ι ℝ L) : ∃ K : ℝ, 0 ≤ K ∧ ∀ Z i, |b.repr Z i| ≤ K * ‖Z‖ := by
  have : FiniteDimensional ℝ L := Module.Finite.of_basis b
  let f : ι → L →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  refine ⟨∑ i, ‖f i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun Z i => ?_⟩
  have h1 : |b.repr Z i| = ‖f i Z‖ := by
    simp [f, Real.norm_eq_abs]
  rw [h1]
  exact ((f i).le_opNorm Z).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => norm_nonneg (f j)) (Finset.mem_univ i)) (norm_nonneg Z))

end Abstract

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}






section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


end



end GlobalTheory.CuspGeo.MeanValue

end
