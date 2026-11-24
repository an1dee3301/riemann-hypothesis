module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IwaPlace

variable {D : D7}


open GlobalTheory.SelfDualAt in
theorem idAt₂ (v : Pl D) : algebraMap (AF D.host.F) (AE D) (cP (· = v)) ∈ idAt D (· = v) := by
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · rw [RingHom.mem_ker]
    show infPart D (cP (· = v) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    exact TensorProduct.zero_tmul _ _
  · rw [RingHom.mem_ker]
    show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w.1 (finPart D (algebraMap (AF D.host.F) (AE D) (cP (· = v)))) = 0
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.LatVac.finPart_tmul]
    have h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w.1 (sndA D.host.F (cP (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
        evalV D.host.F w.1 (indP (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E) := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]
      rfl
    rw [h, evalV_indP, if_neg w.2]
    exact TensorProduct.zero_tmul _ _


open GlobalTheory.SelfDualAt in
theorem eq_alg_cP {v : Pl D} {ε : AE D} (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) :
    ε = algebraMap (AF D.host.F) (AE D) (cP (· = v)) := by
  have h1 := algebraMap_placeIdempotent_mul (· = v) ε hεI.1
  have h2 := (hε _).1 (idAt₂ v)
  rw [← h2, mul_comm]
  exact h1.symm


open GlobalTheory.SelfDualAt in
theorem placeIdem_eq_cP {v : Pl D} {εF : AF D.host.F} (h : IsPlaceIdem D v εF) : εF = cP (· = v) := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  unfold cP
  congr 1
  refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
  show evalV D.host.F w α = evalV D.host.F w (indP (· = v))
  rw [evalV_indP]
  by_cases hw : w = v
  · subst hw; rw [if_pos rfl, h1]
  · rw [if_neg hw, h0 w hw]

theorem half_mem_int (v : Pl D) (h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal) :
    algebraMap D.host.F (Fv D.host.F v) (2⁻¹) ∈ v.adicCompletionIntegers D.host.F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e1 : Valued.v (algebraMap D.host.F (Fv D.host.F v) 2⁻¹) = v.valuation D.host.F 2⁻¹ :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have e2 : v.valuation D.host.F (2 : D.host.F) = 1 := by
    have := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) v (2 : 𝓞 D.host.F)
    simp only [map_ofNat] at this
    rw [this]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 h2
  rw [e1, map_inv₀, e2, inv_one]


open GlobalTheory.SelfDualAt in
theorem exists_trace_one_at_tame : ∀ (D : D7) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε)
    (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), Tame D v →
    ∃ w ∈ intAt D (· = v), w + cA D w = ε := by
  intro D v ε _ _ hεI hε ht
  have hεη := eq_alg_cP hεI hε
  rcases ht.2 with h2 | ⟨e, εF, hsp, hpl, hsum⟩
  · refine ⟨algebraMap (AF D.host.F) (AE D) (cP (· = v) * algebraMap D.host.F (AF D.host.F) 2⁻¹), ⟨?_, ?_⟩, ?_⟩
    · rw [map_mul]
      exact Ideal.mul_mem_right _ _ (idAt₂ v)
    · rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.LatVac.finPart_tmul]
      refine AddSubgroup.subset_closure ⟨sndA D.host.F (cP (· = v) * algebraMap D.host.F (AF D.host.F) 2⁻¹), fun w => ?_, 1, by simp⟩
      rw [map_mul, AlgHom.commutes, map_mul]
      show evalV D.host.F w (indP (· = v)) * _ ∈ _
      rw [evalV_indP]
      by_cases hw : w = v
      · subst hw
        rw [if_pos rfl, one_mul, AlgHom.commutes]
        exact half_mem_int w h2
      · rw [if_neg hw, zero_mul]
        exact zero_mem _
    · rw [cA_alg, ← map_add (f := _), hεη]
      congr 1
      rw [← two_mul, mul_left_comm, ← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul,
        mul_inv_cancel₀ two_ne_zero, map_one, mul_one]
  · have hs : e + cA D e = ε := by rw [hsum, placeIdem_eq_cP hpl, hεη]
    refine ⟨e, ⟨?_, ?_⟩, hs⟩
    · have : e * ε = e := by rw [← hs, mul_add, hsp.1, hsp.2.1, add_zero]
      rw [← this]
      exact Ideal.mul_mem_left _ _ hεI.1
    · exact GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hsp.1])

end GlobalTheory.IwaPlace

end
