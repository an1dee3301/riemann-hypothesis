module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationAlgHomEqOfInertPrime
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.SatakeDualWeyl.StatementG
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
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
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.Basic

@[expose] public section

open NumberField IsDedekindDomain
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_algHom_eq_of_inertPrime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ x : E, w.valuation E (σ x) = w.valuation E x := by
  first | exact @GlobalTheory.InertConjVal.val_conj | exact GlobalTheory.InertConjVal.val_conj | (intros; apply GlobalTheory.InertConjVal.val_conj <;> assumption)
