module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import Development.Core20Slim.GroundTheory.GlobalFields.CompletionAtPlace
public import Development.Core20Slim.GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.LocalFields.Interface
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.IsSimpleRing
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Range
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Range
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Monoid.Units
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Order.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.Topology.ClusterPt
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.Defs

set_option synthInstance.maxHeartbeats 400000

@[expose] public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel

open scoped WithZero

namespace GroundTheory.Global

section Residue

variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

def ringOfIntegersToInteger : 𝓞 F →+* 𝒪[u.adicCompletion F] :=
  ((algebraMap F (u.adicCompletion F)).comp (algebraMap (𝓞 F) F)).codRestrict
    𝒪[u.adicCompletion F] fun r ↦ (mem_valuationInteger_iff u _).2 (coe_algebraMap_mem (𝓞 F) F u r)

@[simp]
theorem coe_ringOfIntegersToInteger (r : 𝓞 F) :
    (ringOfIntegersToInteger u r : u.adicCompletion F) =
      algebraMap F (u.adicCompletion F) (algebraMap (𝓞 F) F r) :=
  rfl

def toResidueInteger : 𝓞 F →+* 𝒪[u.adicCompletion F] ⧸ 𝓂[u.adicCompletion F] :=
  (Ideal.Quotient.mk _).comp (ringOfIntegersToInteger u)

theorem ker_toResidueInteger : RingHom.ker (toResidueInteger u) = u.asIdeal := by
  ext r
  rw [RingHom.mem_ker, toResidueInteger, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
    mem_maximalIdeal_iff_valued_lt_one, coe_ringOfIntegersToInteger]
  erw [valuedAdicCompletion_eq_valuation' u]
  exact valuation_lt_one_iff_mem u r

theorem toResidueInteger_surjective : Function.Surjective (toResidueInteger u) := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hy : (y : u.adicCompletion F) ∈ u.adicCompletionIntegers F :=
    (mem_valuationInteger_iff u _).1 y.2
  have hn : {z : u.adicCompletion F | Valued.v.restrict (z - y) < 1} ∈
      nhds (y : u.adicCompletion F) :=
    Valued.mem_nhds.2 ⟨1, subset_rfl⟩
  obtain ⟨_, hz, r, rfl⟩ := mem_closure_iff_nhds.1
    (adicCompletionIntegers_subset_closure_ringOfIntegers u hy) _ hn
  refine ⟨r, (Ideal.Quotient.eq.2 ?_)⟩
  rw [mem_maximalIdeal_iff_valued_lt_one]
  change Valued.v ((ringOfIntegersToInteger u r : u.adicCompletion F) - (y : u.adicCompletion F)) < 1
  rw [coe_ringOfIntegersToInteger]
  simpa [Valuation.restrict_lt_one_iff] using hz

def residueEquivInteger : (𝓞 F ⧸ u.asIdeal) ≃+* (𝒪[u.adicCompletion F] ⧸ 𝓂[u.adicCompletion F]) :=
  (Ideal.quotEquivOfEq (ker_toResidueInteger u).symm).trans
    (RingHom.quotientKerEquivOfSurjective (toResidueInteger_surjective u))

@[simp]
theorem residueEquivInteger_mk (r : 𝓞 F) :
    residueEquivInteger u (Ideal.Quotient.mk u.asIdeal r) =
      Ideal.Quotient.mk _ (ringOfIntegersToInteger u r) :=
  rfl

end Residue

section Degree

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem algebraMap_ringOfIntegersToInteger (r : 𝓞 K) :
    algebraMap 𝒪[v.adicCompletion K] 𝒪[w.adicCompletion L] (ringOfIntegersToInteger v r) =
      ringOfIntegersToInteger w (algebraMap (𝓞 K) (𝓞 L) r) := by
  apply Subtype.ext
  rw [GroundTheory.LocalField.coe_algebraMap_integer, coe_ringOfIntegersToInteger,
    coe_ringOfIntegersToInteger, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
  rfl

theorem inertiaDeg_integer :
    𝓂[w.adicCompletion L].inertiaDeg 𝒪[v.adicCompletion K] = w.asIdeal.inertiaDeg (𝓞 K) := by
  have := w.isMaximal
  have := v.isMaximal
  rw [Ideal.inertiaDeg_eq_of_isMaximal 𝓂[v.adicCompletion K] 𝓂[w.adicCompletion L],
    Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
  refine (Algebra.finrank_eq_of_equiv_equiv (residueEquivInteger v) (residueEquivInteger w)
    ?_).symm
  apply Ideal.Quotient.ringHom_ext
  ext r
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    residueEquivInteger_mk]
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.algebraMap_mk_of_liesOver,
    residueEquivInteger_mk, algebraMap_ringOfIntegersToInteger]

theorem finrank_adicCompletion :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by
  rw [← ramificationIdx_mul_inertiaDeg_integer v w, ramificationIdx_integer v w,
    inertiaDeg_integer v w]

end Degree

section Check

open AdicLiesOver

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

end Check

end GroundTheory.Global
