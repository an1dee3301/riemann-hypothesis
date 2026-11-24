module

public import Mathlib
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MatrixTransvectionDiagonalDecompositionStatement
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarInvariantUnderTransvectionStatement
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular

@[expose] public section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.ModDet

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K]

theorem map_mul_unit (lam : Measure K) [lam.IsAddHaarMeasure] (u : Kˣ) :
    lam.map (fun y => (u : K) * y) = (distribHaarChar K u)⁻¹ • lam := by
  have hm : Measurable (fun y : K => (u : K) * y) :=
    (continuous_const.mul continuous_id).measurable
  ext s hs
  rw [Measure.map_apply hm hs, Measure.smul_apply, Measure.nnreal_smul_coe_apply, ← map_inv,
    distribHaarChar_mul lam u⁻¹ s]
  congr 1
  ext y
  simp [Set.mem_inv_smul_set_iff, Units.smul_def]

theorem pi_smul_const {ι : Type} [Fintype ι] (lam : Measure K) [SigmaFinite lam] (c : ι → ℝ≥0) :
    Measure.pi (fun i => c i • lam) = (∏ i, c i) • Measure.pi (fun _ : ι => lam) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    ENNReal.ofNNReal_finsetProd]

theorem pi_map_diag {ι : Type} [Fintype ι] (lam : Measure K) [lam.IsAddHaarMeasure] (D : ι → Kˣ) :
    (Measure.pi fun _ : ι => lam).map (fun x i => (D i : K) * x i) =
      (∏ i, (distribHaarChar K (D i))⁻¹) • Measure.pi fun _ : ι => lam := by
  have hm : ∀ i, Measurable (fun y : K => (D i : K) * y) := fun i =>
    (continuous_const.mul continuous_id).measurable
  have hs : ∀ i, SigmaFinite (lam.map (fun y : K => (D i : K) * y)) := fun i => by
    rw [map_mul_unit]; infer_instance
  rw [Measure.pi_map_pi (fun i => (hm i).aemeasurable)]
  simp_rw [map_mul_unit]
  exact pi_smul_const lam _

theorem smul_cancel (lam : Measure K) [lam.IsAddHaarMeasure] {a b : ℝ≥0}
    (h : a • lam = b • lam) : a = b := by
  obtain ⟨C, hC, hn⟩ := exists_compact_mem_nhds (0 : K)
  have h0 : lam C ≠ 0 := (Measure.measure_pos_of_mem_nhds lam hn).ne'
  have h1 : lam C ≠ ∞ := hC.measure_lt_top.ne
  have e := congrArg (fun m : Measure K => m C) h
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at e
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 h1).1 e)

theorem map_transvections {ι : Type} [Fintype ι] [DecidableEq ι] (μ : Measure (ι → K))
    [μ.IsAddHaarMeasure] (L : List (Matrix.TransvectionStruct ι K)) :
    μ.map (fun x => (L.map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) = μ := by
  induction L with
  | nil => simp
  | cons t L ih =>
    have hm : ∀ M : Matrix ι ι K, Measurable (fun x : ι → K => M *ᵥ x) := fun M =>
      (continuous_const.matrix_mulVec continuous_id).measurable
    have e : (fun x : ι → K => ((t :: L).map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) =
        (fun x => t.toMatrix *ᵥ x) ∘
          (fun x => (L.map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) := by
      funext x
      simp [Matrix.mulVec_mulVec]
    rw [e, ← Measure.map_map (hm _) (hm _), ih]
    exact GlobalTheory.T.haar_invariant_under_transvection K ι μ t

theorem det_transvections {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : List (Matrix.TransvectionStruct ι K)) :
    ((L.map Matrix.TransvectionStruct.toMatrix).prod).det = 1 := by
  induction L with
  | nil => simp
  | cons t L ih => simp [Matrix.det_mul, ih, Matrix.TransvectionStruct.det]

theorem map_mulVec_eq_smul : ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K]
    [BorelSpace K] [IsArtinianRing K] [IsReduced K] (ι : Type) [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → K)) [μ.IsAddHaarMeasure] (lam : Measure K) [lam.IsAddHaarMeasure]
    (A : Matrix ι ι K), IsUnit A.det → ∀ c : ℝ≥0,
      lam.map (fun y => A.det * y) = c • lam → μ.map (fun x => A *ᵥ x) = c • μ := by
  intro K _ _ _ _ _ _ _ _ _ _ ι _ _ μ _ lam _ A hA c hc
  obtain ⟨L, L', D, hAeq⟩ := GlobalTheory.T.matrix_transvection_diagonal_decomposition K ι A
  have hdet : A.det = ∏ i, D i := by
    rw [hAeq, Matrix.det_mul, Matrix.det_mul, det_transvections, det_transvections,
      Matrix.det_diagonal, one_mul, mul_one]
  have hu : ∀ i, IsUnit (D i) := fun i => by
    have h := hA
    rw [hdet, ← Finset.mul_prod_erase Finset.univ D (Finset.mem_univ i)] at h
    exact isUnit_of_mul_isUnit_left h
  obtain ⟨Du, hDu⟩ : ∃ Du : ι → Kˣ, ∀ i, (Du i : K) = D i :=
    ⟨fun i => (hu i).unit, fun i => (hu i).unit_spec⟩
  have hcc : (∏ i, (distribHaarChar K (Du i))⁻¹) = c := by
    refine smul_cancel lam ?_
    rw [← hc, hdet]
    have e : (∏ i, D i) = ((∏ i, Du i : Kˣ) : K) := by
      simp [Units.coe_prod, hDu]
    rw [e, map_mul_unit, map_prod, Finset.prod_inv_distrib]
  have hμ := Measure.isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : ι => lam)
  have hmd : Measurable (fun (x : ι → K) i => (Du i : K) * x i) :=
    (continuous_pi fun i => continuous_const.mul (continuous_apply i)).measurable
  have hdiag : μ.map (fun (x : ι → K) i => (Du i : K) * x i) = c • μ := by
    rw [hμ, Measure.map_smul, pi_map_diag, hcc, smul_comm]
    exact hmd.aemeasurable
  have hm : ∀ M : Matrix ι ι K, Measurable (fun x : ι → K => M *ᵥ x) := fun M =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have e : (fun x : ι → K => A *ᵥ x) =
      (fun x => (L.map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) ∘
        (fun (x : ι → K) i => (Du i : K) * x i) ∘
          (fun x => (L'.map Matrix.TransvectionStruct.toMatrix).prod *ᵥ x) := by
    funext x
    have hd : ∀ y : ι → K, (fun i => (Du i : K) * y i) = Matrix.diagonal D *ᵥ y := fun y => by
      funext i
      simp [Matrix.mulVec_diagonal, hDu]
    simp only [Function.comp_apply, hd, Matrix.mulVec_mulVec]
    rw [hAeq, Matrix.mul_assoc]
  rw [e, ← Measure.map_map (hm _) (hmd.comp (hm _)), ← Measure.map_map hmd (hm _),
    map_transvections μ L', hdiag, Measure.map_smul, map_transvections μ L]
  exact (hm _).aemeasurable

end GlobalTheory.CompanionTheory.SW.ModDet
