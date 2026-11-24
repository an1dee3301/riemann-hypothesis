module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.FlagAct


variable {D : D7} {c : Com D} {s : PiLocalization₂ D}

theorem not_isConjPl_of_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P) :
    ∀ PP ∈ P, ∀ PP' ∈ P, ¬ Lev.IsConjPl PP PP' := by
  classical
  intro PP hP PP' hP' hc
  obtain ⟨⟨es, hes, he⟩, h0⟩ := h
  have hsum : ∑ x ∈ P ×ˢ P, es x.1 * cA D (es x.2) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_product, ← h0, he, map_sum, Finset.sum_mul_sum]
  have hidem : ∀ x ∈ P ×ˢ P,
      (es x.1 * cA D (es x.2)) * (es x.1 * cA D (es x.2)) = es x.1 * cA D (es x.2) := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hx
    rw [mul_mul_mul_comm, ← map_mul, (hes _ h1).1.1, (hes _ h2).1.1]
  have horth : es PP * cA D (es PP') = 0 :=
    GlobalTheory.PlaceVec.idem_eq_zero_of_sum (A := AE D) (ι := Pl D.host.E × Pl D.host.E)
      (fun n z hn hz => GlobalTheory.PlaceVec.natCast_mul_eq_zero (D := D) n z hn hz) (fun x => es x.1 * cA D (es x.2)) (P ×ˢ P)
      hidem hsum (PP, PP') (Finset.mem_product.2 ⟨hP, hP'⟩)
  have hfw : ∀ x, x ∈ PP.asIdeal → Formalism.L2.Col.cO D.host.E x ∈ PP'.asIdeal := by
    intro x hx
    obtain ⟨c', hc', hcv⟩ := hc x hx
    have e1 : c' = Formalism.L2.Col.cO D.host.E x := RingOfIntegers.ext hcv
    rw [← e1]; exact hc'
  have hiff : ∀ x, x ∈ PP.asIdeal ↔ Formalism.L2.Col.cO D.host.E x ∈ PP'.asIdeal := by
    have hle : PP.asIdeal ≤ PP'.asIdeal.comap (Formalism.L2.Col.cO D.host.E) := fun x hx => hfw x hx
    haveI := PP'.isPrime
    have heq := PP.isMaximal.eq_of_le (Ideal.IsPrime.comap (Formalism.L2.Col.cO D.host.E)).ne_top hle
    intro x
    rw [heq]
    exact Ideal.mem_comap
  have hconj := GlobalTheory.MovedIdem.isIdemAt_conj (hes PP' hP') hiff
  have heq : es PP = cA D (es PP') :=
    (GlobalTheory.ExportSeries.idemAt_eq (hes PP hP)).symm.trans (GlobalTheory.ExportSeries.idemAt_eq hconj)
  have hz : es PP = 0 := by
    calc es PP = es PP * es PP := ((hes PP hP).1.1).symm
      _ = es PP * cA D (es PP') := congrArg (es PP * ·) heq
      _ = 0 := horth
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot PP.ne_bot
  have h3 := ((hes PP hP).2 x hx0).1 hxP
  rw [hz, zero_mul, map_zero] at h3
  exact h3 (zero_mem _)


end GlobalTheory.ChainOnto.FlagAct
