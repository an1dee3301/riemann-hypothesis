module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousOfValuationEq
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain

open WithZero

namespace GlobalTheory.DenseCompl

section DVR

variable {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [IsFractionRing W Qq]





end DVR





open scoped WithZeroTopology in
theorem exists_extension {K : Type} [Field K] [NumberField K] {R L : Type} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (w : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum R) (f : K →+* u.adicCompletion L)
    (hf : ∀ x, Valued.v (f x) = w.valuation K x) :
    ∃ φ : w.adicCompletion K →+* u.adicCompletion L, Continuous φ ∧
      (∀ x : K, φ (algebraMap K _ x) = f x) ∧ ∀ y, Valued.v (φ y) = Valued.v y := by
  first
  | exact @_root_.GlobalTheory.ValuationExtensionContinuous.exists_extension
  | exact _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension
  | (apply _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ValuationExtensionContinuous.exists_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ValuationExtensionContinuous.exists_extension ..)

end GlobalTheory.DenseCompl
