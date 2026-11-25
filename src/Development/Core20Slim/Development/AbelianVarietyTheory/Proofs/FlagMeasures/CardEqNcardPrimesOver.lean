module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianPerpSubgroup
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Prime.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Insert
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped TensorProduct ENNReal Pointwise
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.SplitResidue

theorem card_eq_ncard_primesOver (E : Type) [Field E] [NumberField E] {g : ℕ} (hg : g.Prime) :
    Nat.card {w : HeightOneSpectrum (𝓞 E) // (g : 𝓞 E) ∈ w.asIdeal} =
      (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 E)).ncard := by
  have hp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  haveI : (Ideal.span {(g : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hne : (Ideal.span {(g : ℤ)}) ≠ ⊥ := by simpa using hg.ne_zero
  haveI hmax : (Ideal.span {(g : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨w.1.asIdeal, w.1.isPrime, ?_⟩) ⟨?_, ?_⟩)
  · haveI := w.1.isPrime
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using w.2
  · intro a b h
    exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  · rintro ⟨P, hP, hPl⟩
    refine ⟨⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hne P⟩, ?_⟩, rfl⟩
    simpa using (Ideal.mem_of_liesOver P (Ideal.span {(g : ℤ)}) (g : ℤ)).1
      (Ideal.mem_span_singleton_self _)


end GlobalTheory.SplitResidue
