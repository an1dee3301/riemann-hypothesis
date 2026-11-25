module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VectorTupleProductMeasureTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Closure
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.ModuArtin

theorem addEquivAddHaarChar_mulVecCE (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [LocallyCompactSpace B] [T2Space B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B] :
    IsArtinianRing B → IsReduced B → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] [MeasurableSpace (κ → B)]
      [BorelSpace (κ → B)] (M : Matrix κ κ B) (hM : IsUnit M.det),
      addEquivAddHaarChar (mulVecCE M hM) = modu B M.det := by
  intro hA hR κ _ _ inst hB M hM
  have heq : inst = MeasurableSpace.pi := by
    exact hB.measurable_eq.trans (@BorelSpace.measurable_eq (κ → B) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst heq
  set ν : Measure B := Measure.addHaar
  set μ : Measure (κ → B) := Measure.pi fun _ : κ => ν
  have h1 := addEquivAddHaarChar_smul_map μ (mulVecCE M hM)
  have h2 : (modu B M.det : ℝ≥0∞) • Measure.map M.mulVec μ = μ :=
    GlobalTheory.GaugeEx.ModDet.smul_map_mulVec_pi ν M hM
  have hfun : ⇑(mulVecCE M hM) = M.mulVec := funext fun x => mulVecCE_apply M hM x
  rw [hfun] at h1
  obtain ⟨K⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts (κ → B)))
  have hpos : μ K ≠ 0 := ((isOpen_interior.measure_pos μ K.interior_nonempty).trans_le
    (measure_mono interior_subset)).ne'
  have hfin : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  set m := (Measure.map M.mulVec μ) (K : Set (κ → B))
  have e1 : (addEquivAddHaarChar (mulVecCE M hM) : ℝ≥0∞) * m = μ K := by
    conv_rhs => rw [← h1]
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have e2 : (modu B M.det : ℝ≥0∞) * m = μ K := by
    conv_rhs => rw [← h2]
    rw [Measure.smul_apply, smul_eq_mul]
  have hm0 : m ≠ 0 := by
    intro h; rw [h, mul_zero] at e1; exact hpos e1.symm
  have hmt : m ≠ ⊤ := by
    intro h
    rw [h] at e1
    have hc : (addEquivAddHaarChar (mulVecCE M hM) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (addEquivAddHaarChar_pos (mulVecCE M hM)).ne'
    rw [ENNReal.mul_top hc] at e1
    exact hfin e1.symm
  have := (ENNReal.mul_left_inj hm0 hmt).1 (e1.trans e2.symm)
  exact_mod_cast this

end GlobalTheory.ModuArtin
