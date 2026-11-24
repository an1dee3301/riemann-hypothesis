module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerDenominatorNotMemOfValuationLeOne
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Valuation.Basic

@[expose] public section

open NumberField IsDedekindDomain
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_denominator_not_mem_of_valuation_le_one : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : E), w.valuation E a ≤ 1 → ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r := by
  first | exact @GlobalTheory.IntegralDenom.exists_denom_not_mem | exact GlobalTheory.IntegralDenom.exists_denom_not_mem | (intros; apply GlobalTheory.IntegralDenom.exists_denom_not_mem <;> assumption)
