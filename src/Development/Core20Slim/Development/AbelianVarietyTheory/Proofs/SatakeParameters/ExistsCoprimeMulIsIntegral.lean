module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecAct
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Order
public import Init.Data.Nat.Coprime
public import Init.Data.Nat.Div.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Basic

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

noncomputable section

namespace GlobalTheory.KerTie.MuqUnit


theorem exists_coprime_mul_isIntegral {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) (x : K)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ w.asIdeal → w.valuation K x ≤ 1) :
    ∃ M : ℕ, M.Coprime p ∧ IsIntegral ℤ ((M : K) * x) := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  have hd0 : y.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hy0
  have hdint : IsIntegral ℤ ((y.natAbs : K) * x) := by
    rcases Int.natAbs_eq y with e | e
    · have e2 : ((y.natAbs : ℤ) : K) = (y : K) := congrArg (fun z : ℤ => (z : K)) e.symm
      have : (y.natAbs : K) * x = y • x := by
        rw [zsmul_eq_mul, ← e2, Int.cast_natCast]
      rw [this]; exact hyint
    · have : (y.natAbs : K) * x = -(y • x) := by
        rw [zsmul_eq_mul, ← neg_mul]; congr 1
        have e' : (y : K) = -((y.natAbs : ℤ) : K) := by
          have := congrArg (fun z : ℤ => (z : K)) e
          simpa using this
        rw [e', neg_neg, Int.cast_natCast]
      rw [this]; exact hyint.neg
  obtain ⟨e, M, hpM, hd⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 p hp.ne_one
  refine ⟨M, (Nat.Prime.coprime_iff_not_dvd hp).2 hpM |>.symm, ?_⟩
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K ((M : K) * x) fun w => by
    by_cases hw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal
    · rw [map_mul]
      refine mul_le_one' ?_ (h w hw)
      have := w.valuation_le_one (K := K) (M : 𝓞 K)
      simpa using this
    · obtain ⟨s, hs⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K ((y.natAbs : K) * x) fun v => by
        obtain ⟨t, ht⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 K) (R := ℤ) (B := K)).1 hdint
        rw [← ht]; exact v.valuation_le_one t
      have hp1 : w.valuation K (p : K) = 1 := by
        have := (w.intValuation_eq_one_iff (x := ((p : ℕ) : 𝓞 K))).2 hw
        rw [← map_natCast (algebraMap (𝓞 K) K), HeightOneSpectrum.valuation_of_algebraMap]
        exact this
      have hle : w.valuation K ((y.natAbs : K) * x) ≤ 1 := by rw [← hs]; exact w.valuation_le_one s
      rw [hd, Nat.cast_mul, Nat.cast_pow, mul_assoc, map_mul, map_pow, hp1, one_pow, one_mul] at hle
      exact hle
  rw [← hr]
  exact RingOfIntegers.isIntegral_coe r


end GlobalTheory.KerTie.MuqUnit

namespace GlobalTheory.KerTie.MuqUnit

open GlobalTheory.CharVal

variable {X : Fields} {Pr : Primes X} {m : ℕ} {Ch : Chars X Pr m} {σ₀ : X.K →+* ℂ} {e : X.Tau → ℚ} {j : Fin m}
  {μ : Formalism.L2.Host.HChar X.E}



end GlobalTheory.KerTie.MuqUnit

namespace GlobalTheory.KerTie.MuqUnit

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}


end GlobalTheory.KerTie.MuqUnit

namespace GlobalTheory.KerTie

open MuqUnit


end GlobalTheory.KerTie
