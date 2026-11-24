module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.PairingDivisors.StatementH
public import Formalism.PairingDivisors.StatementN
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.LemmasAux
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Nat
public import Mathlib.Order.Notation
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Multiplicity

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (betaBound_vp cE_vp c_vp delta_vp a0 n_vp IsClassZetaVals)
open GlobalTheory.CMVal (OF IsBaseCond expIn)

namespace GlobalTheory.DenExist

section Field

variable {E : Type} [Field E] [NumberField E]

theorem finite_support (d s : ℕ) {I : Type} [Fintype I] (κ : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : 𝔣 ≠ ⊥)
    (z : ClassGroup (OF E) → ℚ) :
    {l : ℕ | l.Prime ∧ (⌈betaBound_vp d s κ 𝔣 z l / 12⌉₊ : ℕ) ≠ 0}.Finite := by
  set A : Set ℕ := {l | l.Prime ∧ ∃ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 ∧ (l : OF E) ∈ v.asIdeal} with hAdef
  have hA : A.Finite :=
    GlobalTheory.FunObj.SqNum.finite_primes_under (K := maximalRealSubfield E) (p := fun v => v.asIdeal ∣ 𝔣)
      (Ideal.finite_factors h𝔣)
  let B : Finset ℕ := (Finset.univ.biUnion fun C =>
    (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E)).den.primeFactors) ∪ (discr E).natAbs.primeFactors
  refine (hA.union B.finite_toSet).subset ?_
  rintro l ⟨hl, hn⟩
  by_contra hc
  simp only [Set.mem_union, not_or, Finset.mem_coe] at hc
  obtain ⟨hlA, hlB⟩ := hc
  apply hn
  have hv : ∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → ¬ v.asIdeal ∣ 𝔣 :=
    fun v h1 h2 => hlA ⟨hl, v, h2, h1⟩
  have ha0 : a0 𝔣 l = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply csSup_le'
    rintro _ ⟨v, h1, rfl⟩
    simp [expIn, multiplicity_eq_zero_of_not_dvd (hv v h1)]
  have hcv : c_vp 𝔣 l = 0 := by
    have hd : ¬ l ∣ (discr E).natAbs := fun h => hlB (Finset.mem_union_right _
      (Nat.mem_primeFactors.2 ⟨hl, h, by simpa using discr_ne_zero E⟩))
    rw [c_vp, if_neg (fun ⟨v, h1, h2⟩ => hv v h1 h2), delta_vp]
    simp [padicValInt, padicValNat.eq_zero_of_not_dvd hd]
  have hcE : cE_vp l z = 0 := by
    rw [cE_vp, ← bot_eq_zero, Finset.sup_eq_bot_iff]
    intro C _
    set q := z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E)
    have hd : ¬ l ∣ q.den := fun h => hlB (Finset.mem_union_left _ (Finset.mem_biUnion.2
      ⟨C, Finset.mem_univ _, Nat.mem_primeFactors.2 ⟨hl, h, q.den_ne_zero⟩⟩))
    show (-padicValRat l q).toNat = 0
    rw [Int.toNat_eq_zero, padicValRat, padicValNat.eq_zero_of_not_dvd hd]
    simp
  simp [betaBound_vp, hcE, hcv, ha0, n_vp]

end Field

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

theorem exists_denom (hz : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) (G : GridData Lc sc) (hcm : IsCMField D.host.E)
    (hb : IsBaseCond (condF G.pl)) (i j : Fin D.R.m) (s : ℕ) (hs : 1 ≤ s) :
    ∃ n, IsDenom G i j s n ∧ {l | l.Prime ∧ n l ≠ 0}.Finite := by
  obtain ⟨⟨z, hz'⟩, -⟩ := @hz D.host.E _ _ hcm s hs
  refine ⟨fun l => ((⌈betaBound_vp D.host.d s (kap D sc.cGap i j s) (condF G.pl) z l / 12⌉₊ : ℕ) : ℝ),
    ⟨z, hz', fun l _ => rfl⟩, ?_⟩
  refine (finite_support D.host.d s (kap D sc.cGap i j s) (condF G.pl) hb.1 z).subset ?_
  rintro l ⟨hl, h⟩
  exact ⟨hl, fun h' => h (by simp only [h', Nat.cast_zero])⟩

theorem denEx (hz : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) (hF : FieldDat) : DenEx := by
  obtain ⟨CF0, h⟩ := hF
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF hCF
  refine ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  obtain ⟨hcm, -, -, hb, -⟩ := h C hC D large₂ he hx hR T Lc μ₀ hL G
  exact fun i j s hs _ => exists_denom hz G hcm hb i j s hs

end GlobalTheory.DenExist

end
