module

public import Mathlib
public import Formalism.LocalToGlobal.HermitianForms.FormsTied
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Formalism.LocalToGlobal.Columns.CoefModAt
public import Formalism.LocalRingCardinality.PosOfIsomEmb
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.FinalW
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Formalism.LocalRingCardinality.DataArith
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsConjAtOfEmbedding
public import Formalism.LocalRingCardinality.DataForms
public import Formalism.LocalRingCardinality.DataKernels
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.QuotientMetricDivisors.Statement
public import Init.Core
public import Init.Data.Nat.Div.Basic
public import Init.Prelude
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem ptField_main : ∀ D : D7, IsTotallyComplex D.what₂.LL ∧ (∃ v0 : InfinitePlace D.what₂.LL, Formalism.DivisionValues.IsConjAt v0) ∧ ∀ (u : D.what₂.Word) (c : (D.fm u).clsP), Nat.card ((D.fm u).stabilizer₂ c) ∣ (D.mem u).C.DGam := by
  intro D
  refine ⟨D.tcLL, GlobalTheory.isConjAt_exists_main D.what₂.LL ⟨D.what₂.embLL, D.starLL_cx⟩, ?_⟩
  intro u c
  exact (Subgroup.card_dvd_of_injective _ ((D.fm u).stabMap_inj c)).trans
    ((D.mem u).C.dvd_DGam _ le_rfl _)

end GlobalTheory
