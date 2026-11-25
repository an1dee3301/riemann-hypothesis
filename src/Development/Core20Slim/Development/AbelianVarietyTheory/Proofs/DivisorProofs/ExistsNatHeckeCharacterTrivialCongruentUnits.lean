module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsUnitaryOfOrder
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.Defs
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.Mem.HeckeLevel

open GlobalTheory.Mem.Chr

theorem exists_level_nat : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L), ∃ M : ℕ, 0 < M ∧ ∀ a : Neutral.B1.Ideles L, a ∈ GlobalTheory.Mem.Chr.unitIdl L → (∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 L), Valued.v ((a : AdeleRing (𝓞 L) L).2 P - 1) ≤ Valued.v ((M : L) : P.adicCompletion L)) → χ.1 a = 1 := by
  intro L _ _ χ
  classical
  obtain ⟨hfin, hlev⟩ := GlobalTheory.Mem.UnrAe.unr_ae_and_level L χ
  choose n hn using hlev
  refine ⟨∏ P ∈ hfin.toFinset, (Ideal.absNorm P.asIdeal) ^ (n P), ?_, ?_⟩
  · refine Finset.prod_pos fun P _ => pow_pos (Nat.pos_of_ne_zero fun h => P.ne_bot ?_) _
    exact Ideal.absNorm_eq_zero_iff.1 h
  · intro a ha h1 hv
    refine GlobalTheory.Mem.LocTriv.eq_one_of_local L χ.1 χ.2.1 a ha h1 fun P x hx => ?_
    have hxu : IsUnitAt P x := by
      unfold IsUnitAt
      rw [hx]
      exact ha P
    by_cases hP : P ∈ hfin.toFinset
    · refine hn P x hxu ?_
      rw [hx]
      refine (hv P).trans ?_
      have e : (((∏ Q ∈ hfin.toFinset, (Ideal.absNorm Q.asIdeal) ^ (n Q) : ℕ) : L) : P.adicCompletion L) =
          (((∏ Q ∈ hfin.toFinset, (Ideal.absNorm Q.asIdeal) ^ (n Q) : ℕ) : 𝓞 L) : L) := by
        push_cast
        rfl
      rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_le_pow_iff_dvd]
      have hd : (Ideal.absNorm P.asIdeal) ^ (n P) ∣ ∏ Q ∈ hfin.toFinset, (Ideal.absNorm Q.asIdeal) ^ (n Q) :=
        Finset.dvd_prod_of_mem _ hP
      have hd' := Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast (α := 𝓞 L) hd)
      refine Ideal.dvd_iff_le.2 (le_trans hd' ?_)
      rw [Nat.cast_pow, ← Ideal.span_singleton_pow]
      refine Ideal.pow_right_mono ?_ _
      rw [Ideal.span_singleton_le_iff_mem]
      exact Ideal.absNorm_mem P.asIdeal
    · have hu : χ.UnrAt P := by
        by_contra h
        exact hP (hfin.mem_toFinset.2 h)
      exact hu x hxu

end GlobalTheory.Mem.HeckeLevel
