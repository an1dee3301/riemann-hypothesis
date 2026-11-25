module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleScaling
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.AdeleMeasure
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Torsor
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ModuAdele

open scoped Pointwise

theorem distribHaarChar_adeleRing (K : Type) [Field K] [NumberField K] (a : (AdeleRing (𝓞 K) K)ˣ) :
    (distribHaarChar (AdeleRing (𝓞 K) K) a : ℝ) = (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) := by
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := GroundTheory.Global.measurableSpace_adeleRing K
  obtain ⟨s, hsc, hs0⟩ : ∃ s : Set (AdeleRing (𝓞 K) K), IsCompact s ∧ s ∈ nhds (0 : AdeleRing (𝓞 K) K) :=
    exists_compact_mem_nhds 0
  have hpos : 0 ≤ (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) := (GroundTheory.Global.IdeleGroup.ideleModule K a).2.le
  set r : NNReal := ⟨_, hpos⟩ with hr
  set μ := GroundTheory.Global.adeleMeasure K with hμ
  set ν : Measure (AdeleRing (𝓞 K) K) := Measure.addHaar with hν
  have e1 := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure μ ν hsc.closure
  have e2 := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure μ ν (hsc.smul a).closure
  have hm := GroundTheory.Global.adeleMeasure_smul a s
  set c := μ.addHaarScalarFactor ν
  have hμs : μ s ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hs0).ne'
  have hνs : ν s ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hs0).ne'
  have hνs' : ν s ≠ ⊤ := hsc.measure_lt_top.ne
  have hc : (c : ENNReal) ≠ 0 := by
    intro h0
    apply hμs
    rw [e1, ENNReal.smul_def, smul_eq_mul, h0, zero_mul]
  have h := distribHaarChar_eq_of_measure_smul_eq_mul (g := a) (μ := ν) (s := s) hνs hνs'
    (r := r) (by
      rw [e1, e2, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul,
        ENNReal.ofReal_eq_coe_nnreal hpos] at hm
      have hm' : (c : ENNReal) * ν (a • s) = (c : ENNReal) * ((r : ENNReal) * ν s) := by
        calc (c : ENNReal) * ν (a • s) = (r : ENNReal) * ((c : ENNReal) * ν s) := hm
          _ = (c : ENNReal) * ((r : ENNReal) * ν s) := by ring
      exact (ENNReal.mul_right_inj hc ENNReal.coe_ne_top).1 hm')
  rw [h]
  rfl

end GlobalTheory.ModuAdele

theorem GlobalTheory.ModuAdele.modu_norm_eq_absE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x : (AE F E)ˣ),
    (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) x) = absE F E x := by
  intro F E _ _ _ _ _ x
  have hf : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖evFin F v (Algebra.norm (AF F) x.1)‖₊).Finite := by
    simpa only [GlobalTheory.Doubling.absEv_unitFin] using GlobalTheory.Doubling.finite_mulSupport_absEv x
  apply NNReal.eq
  change (distribHaarChar (AdeleRing (𝓞 F) F) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) x) : ℝ) = _
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GroundTheory.Global.IdeleGroup.ideleModule_eq, GlobalTheory.Doubling.absE_apply]
  simp only [GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf]
  rw [NNReal.coe_mul, NNReal.coe_prod]
  congr 1
  rw [show ((∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖evFin F v (Algebra.norm (AF F) x.1)‖₊ : ℝ≥0) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((‖evFin F v (Algebra.norm (AF F) x.1)‖₊ : ℝ≥0) : ℝ) from
      NNReal.toRealHom.toMonoidHom.map_finprod hf]
  rfl
