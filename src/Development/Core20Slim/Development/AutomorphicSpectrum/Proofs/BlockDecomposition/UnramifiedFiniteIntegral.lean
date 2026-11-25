module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.BasisSet
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

namespace GlobalTheory.CompanionTheory.Gunr

open NumberField IsDedekindDomain Filter

theorem finInt : PositivityTheory.SiegelWeilFormula.Gunr.FinInt := by
  intro F _ _ X
  have hone : ∀ x : F, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F := by
    intro x
    have hfin : {v : HeightOneSpectrum (𝓞 F) | 1 < v.valuation F x}.Finite :=
      HeightOneSpectrum.Support.finite (𝓞 F) x
    have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ¬ 1 < v.valuation F x := by
      rw [eventually_cofinite]
      simpa using hfin
    refine hev.mono fun v hv => ?_
    have e : Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, e]
    exact not_lt.mp hv
  have hall : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∀ x ∈ X, algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F :=
    (Filter.eventually_all_finset X).2 fun x _ => hone x
  exact hall

end GlobalTheory.CompanionTheory.Gunr
