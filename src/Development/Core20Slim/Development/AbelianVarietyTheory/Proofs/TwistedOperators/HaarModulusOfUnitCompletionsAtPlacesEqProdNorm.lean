module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct Pointwise

namespace GlobalTheory.ModuPiLocal

theorem distribHaarChar_pi {ι : Type} [Fintype ι] (A : ι → Type) [∀ i, CommRing (A i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalRing (A i)] [∀ i, LocallyCompactSpace (A i)]
    [∀ i, T2Space (A i)] [∀ i, SecondCountableTopology (A i)] (u : (∀ i, A i)ˣ) :
    distribHaarChar (∀ i, A i) u = ∏ i, distribHaarChar (A i) (Units.map (Pi.evalRingHom A i).toMonoidHom u) := by
  classical
  letI : ∀ i, MeasurableSpace (A i) := fun i => borel (A i)
  haveI : ∀ i, BorelSpace (A i) := fun i => ⟨rfl⟩
  let μ : ∀ i, Measure (A i) := fun i => Measure.addHaar
  let S : ∀ i, TopologicalSpace.PositiveCompacts (A i) := fun i => Classical.choice inferInstance
  have h0 : ∀ i, μ i (S i : Set (A i)) ≠ 0 := fun i =>
    (Measure.measure_pos_of_nonempty_interior (μ i) (S i).interior_nonempty).ne'
  have h1 : ∀ i, μ i (S i : Set (A i)) ≠ ⊤ := fun i => (S i).isCompact.measure_lt_top.ne
  have hp : ∀ T : ∀ i, Set (A i), (Measure.pi μ) (Set.univ.pi T) = ∏ i, μ i (T i) := fun T =>
    Measure.pi_pi _ _
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := Measure.pi μ)
    (s := Set.univ.pi fun i => (S i : Set (A i)))
    (by rw [hp]; exact Finset.prod_ne_zero_iff.2 fun i _ => h0 i)
    (by rw [hp]; exact ENNReal.prod_ne_top fun i _ => h1 i) ?_
  have e : u • (Set.univ.pi fun i => (S i : Set (A i))) =
      Set.univ.pi fun i => Units.map (Pi.evalRingHom A i).toMonoidHom u • (S i : Set (A i)) := by
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_pi, Set.mem_univ, forall_true_left]
    refine forall_congr' fun i => ?_
    rw [← map_inv]
    rfl
  rw [e, hp, hp]
  push_cast
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [distribHaarChar_mul]

end GlobalTheory.ModuPiLocal

namespace GlobalTheory.ModuPiLocal

theorem modu_sPart : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (x : SPart F S), IsUnit x → (modu (SPart F S) x : ℝ) = ∏ v : S, ‖x v‖ := by
  intro F _ _ S x hx
  rw [modu, dite_eq_left hx, distribHaarChar_pi (fun v : S => Fv F v.1), NNReal.coe_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hv : IsUnit (x v) := (Pi.isUnit_iff.1 hx) v
  have h := GlobalTheory.GaugeProdFormula.modu_finite F v.1 (x v) hv.ne_zero
  rw [modu, dite_eq_left hv] at h
  rw [← h]
  congr 2
  ext
  rfl

end GlobalTheory.ModuPiLocal
