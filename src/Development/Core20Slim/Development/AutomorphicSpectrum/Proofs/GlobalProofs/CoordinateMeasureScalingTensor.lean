module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Lattice
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.HaarScale

theorem unit_mul_map_haar : ∀ (F : Type) [Field F] [NumberField F] (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → ∀ (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → lam.map (fun y => t * y) = (∏ w, ‖e t w‖₊)⁻¹ • lam := by
  intro F _ _ e he lam hlam t ht
  classical
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hc : Continuous e := he.continuous
  let h : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph e
  have hcs : Continuous e.symm := by
    have : (e.symm : (InfinitePlace F → ℝ) → Ainf F) = h.symm := by
      funext y
      have h1 : e (h.symm y) = y := h.apply_symm_apply y
      exact e.symm_apply_eq.2 h1.symm
    rw [this]; exact h.symm.continuous
  have hm : Measurable e := hc.measurable
  have hms : Measurable e.symm := hcs.measurable
  have hmul : Measurable (fun y : Ainf F => t * y) := by
    have : (fun y : Ainf F => t * y) = fun y => e.symm (e t * e y) := by
      funext y; simp
    rw [this]
    exact hcs.measurable.comp (hm.const_mul _)
  obtain ⟨D, hD⟩ : ∃ D : InfinitePlace F → ℝ, D = e t := ⟨_, rfl⟩
  have hDu : IsUnit D := hD ▸ ht.map e
  have hD0 : ∀ w, D w ≠ 0 := fun w => by
    obtain ⟨u, hu⟩ := hDu
    have h1 : D w * (u⁻¹ : (InfinitePlace F → ℝ)ˣ).1 w = 1 := by
      have := congrFun (u.mul_inv) w
      rw [hu] at this
      simpa using this
    exact left_ne_zero_of_mul_eq_one h1
  haveI hμ : (lam.map e).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map lam e.toAddEquiv hc hcs
  let L : (InfinitePlace F → ℝ) →ₗ[ℝ] (InfinitePlace F → ℝ) := Matrix.toLin' (Matrix.diagonal D)
  have hL : ∀ x, L x = D * x := fun x => by
    funext w
    simp [L, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  have hdet : LinearMap.det L = ∏ w, D w := by
    simp [L, LinearMap.det_toLin', Matrix.det_diagonal]
  have hdet0 : LinearMap.det L ≠ 0 := by
    rw [hdet]; exact Finset.prod_ne_zero_iff.2 fun w _ => hD0 w
  have hscale := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := lam.map e) hdet0
  have hconst : ENNReal.ofReal |(LinearMap.det L)⁻¹| = (((∏ w, ‖e t w‖₊)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    have : |(LinearMap.det L)⁻¹| = (((∏ w, ‖e t w‖₊)⁻¹ : ℝ≥0) : ℝ) := by
      rw [hdet, abs_inv, Finset.abs_prod]
      push_cast
      simp [hD]
    rw [this, ENNReal.ofReal_coe_nnreal]
  have key : (lam.map (fun y => t * y)).map e = (∏ w, ‖e t w‖₊)⁻¹ • lam.map e := by
    rw [Measure.map_map hm hmul, ENNReal.smul_def, ← hconst, ← hscale,
      Measure.map_map L.continuous_of_finiteDimensional.measurable hm]
    congr 1
    funext y
    simp [hL, hD]
  have back : ∀ ν : Measure (Ainf F), (ν.map e).map e.symm = ν := fun ν => by
    rw [Measure.map_map hms hm]
    have : (e.symm ∘ e : Ainf F → Ainf F) = id := by funext y; simp
    rw [this, Measure.map_id]
  rw [← back (lam.map fun y => t * y), key, Measure.map_smul, back]
  exact hms.aemeasurable

end GlobalTheory.CompanionTheory.HaarScale
