module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.SatakeDualWeyl.StatementG
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Kleene
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
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Valuation.Basic

@[expose] public section

open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory.InertValRestr

theorem liesOver_of_isInertAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) : w.asIdeal.LiesOver v.asIdeal := by
  refine ⟨?_⟩
  have hP : w.asIdeal.IsPrime := w.isPrime
  have hc : (w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).IsPrime := inferInstance
  refine v.isMaximal.eq_of_le hc.ne_top ?_
  show v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  rw [← hin]
  exact Ideal.le_comap_map

theorem ramificationIdx'_eq_one_of_isInertAt {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
  have hP : w.asIdeal.IsPrime := w.isPrime
  apply Ideal.ramificationIdx'_spec
  · rw [hin, pow_one]
  · rw [hin]
    exact not_le_of_gt (Ideal.pow_succ_lt_pow w.ne_bot 1 |>.trans_eq (pow_one _))

theorem valuation_algebraMap_of_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ x : F, w.valuation E (algebraMap F E x) = v.valuation F x := by
  intro F E _ _ _ _ _ v w hin x
  have := liesOver_of_isInertAt v w hin
  rw [← HeightOneSpectrum.valuation_liesOver (K := F) E v w x,
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
    ramificationIdx'_eq_one_of_isInertAt v w hin, pow_one]

end GlobalTheory.InertValRestr
