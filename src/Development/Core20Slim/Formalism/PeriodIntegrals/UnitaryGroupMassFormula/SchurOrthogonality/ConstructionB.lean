module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.InstMeasurableSpaceMat
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Torsor
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial MeasureTheory Measure TopologicalSpace Matrix

theorem isCompact_unitaryGroup (N : ℕ) :
    IsCompact ((Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ))) := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hK.of_isClosed_subset ?_ ?_
  · have e : (Matrix.unitaryGroup (Fin N) ℂ : Set (Matrix (Fin N) (Fin N) ℂ)) =
        {A : Matrix (Fin N) (Fin N) ℂ | A * star A = 1} := by
      ext A
      exact Matrix.mem_unitaryGroup_iff
    rw [e]
    exact isClosed_eq (continuous_id.matrix_mul continuous_star) continuous_const
  · intro A hA
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact entry_norm_bound_of_unitary hA i j

instance compactSpace_unitaryGroup (N : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin N) ℂ) :=
  isCompact_iff_compactSpace.mp (isCompact_unitaryGroup N)

theorem isMulRightInvariant_of_compact {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsHaarMeasure μ] : IsMulRightInvariant μ := by
  constructor
  intro g
  haveI : (Measure.map (fun x => x * g) μ).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right μ g
  have huniv : Measure.map (fun x => x * g) μ Set.univ = μ Set.univ := by
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
  have hfin : μ Set.univ ≠ ⊤ := measure_ne_top μ _
  have hpos : μ Set.univ ≠ 0 := (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'
  have hc : (Measure.map (fun x => x * g) μ).haarScalarFactor μ = 1 := by
    have h1 := Measure.measure_isHaarMeasure_eq_smul_of_isOpen (Measure.map (fun x => x * g) μ) μ
      isOpen_univ
    rw [huniv, ENNReal.smul_def] at h1
    have h2 : ((((Measure.map (fun x => x * g) μ).haarScalarFactor μ : NNReal) : ENNReal)) = 1 := by
      have h3 : (((Measure.map (fun x => x * g) μ).haarScalarFactor μ : NNReal) : ENNReal) * μ Set.univ =
          1 * μ Set.univ := by
        rw [one_mul]
        exact h1.symm
      exact (ENNReal.mul_left_inj hpos hfin).mp h3
    exact_mod_cast h2
  refine MeasureTheory.ext_of_generate_finite {s : Set G | IsOpen s}
    BorelSpace.measurable_eq isPiSystem_isOpen ?_ huniv
  intro s hs
  rw [Measure.measure_isHaarMeasure_eq_smul_of_isOpen _ μ hs, hc, one_smul]

theorem unitary_haar_measure : HaarU := by
  intro N
  haveI : CompactSpace (Matrix.unitaryGroup (Fin N) ℂ) := compactSpace_unitaryGroup N
  let μG : Measure (Matrix.unitaryGroup (Fin N) ℂ) := Measure.haarMeasure ⊤
  haveI : μG.IsMulRightInvariant := isMulRightInvariant_of_compact μG
  have hm : Measurable (Subtype.val : Matrix.unitaryGroup (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ) :=
    measurable_subtype_coe
  refine ⟨Measure.map Subtype.val μG, ?_, ?_, ?_, ?_⟩
  · constructor
    rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ]
    have h1 := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (Matrix.unitaryGroup (Fin N) ℂ)))
    simpa using h1
  · have hmeas : MeasurableSet {x : Matrix (Fin N) (Fin N) ℂ | x ∈ Matrix.unitaryGroup (Fin N) ℂ} :=
      (isCompact_unitaryGroup N).isClosed.measurableSet
    rw [ae_map_iff hm.aemeasurable hmeas]
    exact Filter.Eventually.of_forall fun y => y.2
  · intro u hu f hf
    have hs : AEStronglyMeasurable (fun x => f (x * u)) (Measure.map Subtype.val μG) :=
      (hf.comp (continuous_mul_const u)).aestronglyMeasurable
    rw [integral_map hm.aemeasurable hs, integral_map hm.aemeasurable hf.aestronglyMeasurable]
    have h1 := integral_mul_right_eq_self (μ := μG)
      (fun y : Matrix.unitaryGroup (Fin N) ℂ => f (y : Matrix (Fin N) (Fin N) ℂ)) ⟨u, hu⟩
    simpa using h1
  · intro u hu f hf
    have hs : AEStronglyMeasurable (fun x => f (u * x)) (Measure.map Subtype.val μG) :=
      (hf.comp (continuous_const_mul u)).aestronglyMeasurable
    rw [integral_map hm.aemeasurable hs, integral_map hm.aemeasurable hf.aestronglyMeasurable]
    have h1 := integral_mul_left_eq_self (μ := μG)
      (fun y : Matrix.unitaryGroup (Fin N) ℂ => f (y : Matrix (Fin N) (Fin N) ℂ)) ⟨u, hu⟩
    simpa using h1

end PI.WSF
