module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOfOrderDvd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertPlace

open GlobalTheory.IdemSupport

theorem inertQ_iff_cP {D : D7} {q : ℕ} (hq : q.Prime) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hqP : (q : 𝓞 D.host.E) ∈ P.asIdeal) : Formalism.MainNotions.StandardLatticesGL3.InertQ D q ↔ cP P = P := by
  constructor
  · intro hI
    exact ((isConjPl_iff P P).1 (GlobalTheory.XiSplit.isConjPl_of_smul_eq (hI P.asIdeal P.isPrime P.ne_bot hqP))).symm
  · intro hc
    by_contra h
    exact GlobalTheory.NormSum.VacInt.conj_smul_ne D hq h P.asIdeal P.isPrime hqP
      (GlobalTheory.XiSplit.smul_eq_of_isConjPl ((isConjPl_iff P P).2 hc.symm))

theorem nonSplitAt_iff_cP {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F}
    (hη : IsPlaceIdem D v η) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : P.under (𝓞 D.host.F) = v) :
    GlobalTheory.WeilParts.NonSplitAt D v η ↔ cP P = P := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨h0, h1, h2⟩ := place_comp hΦ hη
  constructor
  · rintro ⟨-, hns⟩
    by_contra hc
    obtain ⟨e, f, h⟩ := exists_isPrimeIdem hΦ P
    obtain ⟨hd, ε, hε, hf⟩ := of_isPrimeIdem hΦ h
    rw [hP] at hε
    have hεη := placeIdem_unique hε hη
    subst hεη
    rcases h with ⟨h, rfl⟩ | ⟨rfl, -, -⟩
    · exact hns ⟨e, h.1, hf⟩
    · have hd' := delta_conj hΦ hd
      rw [hf, cA_algebraMap, ← hf] at hd'
      have := hd'.2.2 P (Ne.symm hc)
      rw [hd.2.1] at this
      exact one_ne_zero this
  · intro hc
    refine ⟨hη, ?_⟩
    rintro ⟨e, ⟨ee, ec, -⟩, hs⟩
    have he : e * algebraMap (AF D.host.F) (AE D) η = e := by
      rw [← hs, mul_add, ee, ec, add_zero]
    have hi : infPart D e = 0 := by
      rw [← he, RingHom.map_mul, h0, mul_zero]
    have hout : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q ≠ P → Φ e Q = 0 := by
      intro Q hQ
      have hQv : Q.under (𝓞 D.host.F) ≠ v := by
        intro hv
        rcases eq_or_eq_cP (hv.trans hP.symm) with h | h
        · exact hQ h
        · exact hQ (h.trans hc)
      rw [← he, ev_mul, h2 Q hQv, mul_zero]
    have hPP : Φ e P * Φ e P = Φ e P := by rw [← ev_mul, ee]
    have h01 : Φ e P = 0 ∨ Φ e P = 1 := by
      have : Φ e P * (Φ e P - 1) = 0 := by rw [mul_sub, hPP, mul_one, sub_self]
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.1 h)
    rcases h01 with h | h
    · have e0 : e = 0 := by
        refine hΦ.ext e hi (FiniteAdeleRing.ext _ fun Q => ?_)
        by_cases hQ : Q = P
        · subst hQ; rw [h]; rfl
        · rw [hout Q hQ]; rfl
      have := h1 P hP
      rw [← hs, e0, map_zero, add_zero, ev_zero] at this
      exact zero_ne_one this
    · have hd : IsDelta Φ P e := ⟨hi, h, hout⟩
      have hd' := delta_conj hΦ hd
      rw [hc] at hd'
      have hce := delta_unique hΦ hd' hd
      rw [hce, ee] at ec
      rw [ec, ev_zero] at h
      exact zero_ne_one h

theorem inertQ_iff_nonSplitAt : ∀ (D : D7) (q : ℕ), q.Prime → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (η : AF D.host.F), IsPlaceIdem D v η →
    (q : 𝓞 D.host.F) ∈ v.asIdeal → (Formalism.MainNotions.StandardLatticesGL3.InertQ D q ↔ GlobalTheory.WeilParts.NonSplitAt D v η) := by
  intro D q hq v η hη hqv
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 D.host.E)).some
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have hP : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hl.over.symm
  have hqP : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
    have h : (q : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by rw [hP]; exact hqv
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (q : 𝓞 D.host.F) ∈ P.asIdeal at h
    rwa [map_natCast] at h
  rw [inertQ_iff_cP hq P hqP, nonSplitAt_iff_cP hη P hP]

end GlobalTheory.InertPlace
