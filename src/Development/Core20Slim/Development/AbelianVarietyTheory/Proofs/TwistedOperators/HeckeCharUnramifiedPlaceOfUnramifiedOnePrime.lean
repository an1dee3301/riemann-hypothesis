module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingCharactersUnramifiedOffLevels
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleCharRestrictLocalUnitsResidueChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfHeckeCharUnramifi
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SatakeDualWeyl.StatementE
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnramFromOnePrime

open GlobalTheory.IdemSupport GlobalTheory.ResLoc

variable {D : D7}

theorem eq_of_ev {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ) {a b : AE D}
    (hi : infPart D a = infPart D b) (hf : ∀ Q, Φ a Q = Φ b Q) : a = b := by
  refine sub_eq_zero.1 (hΦ.ext (a - b) (by rw [RingHom.map_sub, hi, sub_self]) (FiniteAdeleRing.ext _ fun Q => ?_))
  rw [ev_sub, hf Q, sub_self]
  rfl

theorem eq_one_of_supp {w : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} {χ : (AE D)ˣ →* Circle}
    (h : Formalism.IndefR.Mult.IsPrimeIdem w e f) (hu : GlobalTheory.LFun.UnrAt χ w) (x : (AE D)ˣ)
    (hx : e * ((x : AE D) - 1) = (x : AE D) - 1) (h1 : finPart D (x : AE D) ∈ intAE D)
    (h2 : finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D) : χ x = 1 := by
  obtain ⟨y, hy, rfl⟩ := GlobalTheory.WeilAtPlace.exists_eq_locIdele (GlobalTheory.WeilAtPlace.isPrimeIdem_infPart h)
    (GlobalTheory.LFun.finPart_of_isPrimeIdem h) x hx
  have hy' : ((y⁻¹ : (w.adicCompletion D.host.E)ˣ) : w.adicCompletion D.host.E) =
      GlobalTheory.LFun.compAt D.host.F w (finPart D ((GlobalTheory.LFun.locIdele D.host.F w y)⁻¹ : (AE D)ˣ)) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hy, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have a1 : Valued.v (y : w.adicCompletion D.host.E) ≤ 1 := by
    rw [hy]; exact (GlobalTheory.LFun.mem_intAE_iff_compAt _).1 h1 w
  have a2 : Valued.v ((y⁻¹ : (w.adicCompletion D.host.E)ˣ) : w.adicCompletion D.host.E) ≤ 1 := by
    rw [hy']; exact (GlobalTheory.LFun.mem_intAE_iff_compAt _).1 h2 w
  have hun : Formalism.L2.Host.IsUnitAt w y :=
    GlobalTheory.UnramOver.val_eq_one_of_unit Valued.v (RingHom.id _) y a1 a2
  have := hu y hun
  exact Circle.ext (congrArg Units.val this)

end GlobalTheory.UnramFromOnePrime

namespace GlobalTheory.UnramFromOnePrime

open GlobalTheory.IdemSupport GlobalTheory.ResLoc


set_option maxHeartbeats 1000000 in
theorem unramAt_of_unrAt_one : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → ResEta D ν 0 →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt ν w → GlobalTheory.WeilParts.UnramAt ε ν := by
  classical
  intro D ν _ hR v ε hε w hw hu x hx h1 h2
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨e, f, hp⟩ := exists_isPrimeIdem hΦ w
  obtain ⟨hd, ε', hε', hf⟩ := of_isPrimeIdem hΦ hp
  rw [hw] at hε'
  have pc := place_comp hΦ hε
  have pc' := place_comp hΦ hε'
  have hfε : f = algebraMap (AF D.host.F) (AE D) ε := by
    rw [hf]
    refine eq_of_ev hΦ (by rw [pc.1, pc'.1]) fun Q => ?_
    by_cases hQ : Q.under (𝓞 D.host.F) = v
    · rw [pc.2.1 Q hQ, pc'.2.1 Q hQ]
    · rw [pc.2.2 Q hQ, pc'.2.2 Q hQ]
  have hev : ∀ Q, Φ e Q = if Q = w then 1 else 0 := fun Q => by
    split_ifs with hQ
    · rw [hQ]; exact hd.2.1
    · exact hd.2.2 Q hQ
  have hee : e * e = e := eq_of_ev hΦ (by rw [RingHom.map_mul, hd.1, zero_mul]) fun Q => by
    rw [ev_mul, hev Q]
    split_ifs <;> simp
  have key : (1 - e) * (1 - cA D e) * f = 0 := by
    rcases hp with ⟨-, hfe⟩ | ⟨hfe, -, -⟩
    · have hc2 : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
      rw [hfe]
      linear_combination (cA D e - 1) * hee + (e - 1) * hc2
    · rw [hfe]
      linear_combination (cA D e - 1) * hee
  have hfc : cA D f = f := by rw [hfε]; exact cA_algebraMap ε
  have hx' : f * ((x : AE D) - 1) = (x : AE D) - 1 := by rw [hfε]; exact hx
  have int1 : ∀ Q, Φ (x : AE D) Q ∈ Q.adicCompletionIntegers D.host.E := (hΦ.int _).1 h1
  have int2 : ∀ Q, Φ ((x⁻¹ : (AE D)ˣ) : AE D) Q ∈ Q.adicCompletionIntegers D.host.E := (hΦ.int _).1 h2
  obtain ⟨y, hy, hys⟩ := GlobalTheory.UnrOffLevels.exists_glue hee x
  have hxx : (x : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := Units.mul_inv x
  have hyi : ((y⁻¹ : (AE D)ˣ) : AE D) = e * ((x⁻¹ : (AE D)ˣ) : AE D) + (1 - e) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hy]
    linear_combination (e * e) * hxx + (2 - (x : AE D) - ((x⁻¹ : (AE D)ˣ) : AE D)) * hee
  have cut_int : ∀ z : AE D, (∀ Q, Φ z Q ∈ Q.adicCompletionIntegers D.host.E) →
      ∀ Q, Φ (e * z + (1 - e)) Q ∈ Q.adicCompletionIntegers D.host.E := fun z hz Q => by
    rw [ev_add, ev_mul, ev_sub, ev_one, hev Q]
    split_ifs
    · rw [one_mul, sub_self, add_zero]; exact hz Q
    · rw [zero_mul, sub_zero, zero_add]; exact one_mem _
  have iy1 : ∀ Q, Φ (y : AE D) Q ∈ Q.adicCompletionIntegers D.host.E := by rw [hy]; exact cut_int _ int1
  have iy2 : ∀ Q, Φ ((y⁻¹ : (AE D)ˣ) : AE D) Q ∈ Q.adicCompletionIntegers D.host.E := by
    rw [hyi]; exact cut_int _ int2
  have hνy : ν y = 1 := eq_one_of_supp hp hu y hys ((hΦ.int _).2 iy1) ((hΦ.int _).2 iy2)
  obtain ⟨z, hzdef⟩ : ∃ z : (AE D)ˣ, z = x * y⁻¹ := ⟨_, rfl⟩
  have iz1 : finPart D (z : AE D) ∈ intAE D := (hΦ.int _).2 fun Q => by
    rw [hzdef, Units.val_mul, ev_mul]; exact mul_mem (int1 Q) (iy2 Q)
  have iz2 : finPart D ((z⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := (hΦ.int _).2 fun Q => by
    have hzi : (z⁻¹ : (AE D)ˣ) = y * x⁻¹ := by rw [hzdef, _root_.mul_inv_rev, inv_inv y]
    rw [hzi, Units.val_mul, ev_mul]; exact mul_mem (iy1 Q) (int2 Q)
  have hz1 : (z : AE D) - 1 = (1 - e) * f * ((x : AE D) - 1) := by
    have hzv : (z : AE D) = (x : AE D) * ((y⁻¹ : (AE D)ˣ) : AE D) := by rw [hzdef, Units.val_mul]
    rw [hzv, hyi]
    linear_combination e * hxx - (1 - e) * hx'
  have hcz : cA D (z : AE D) - 1 = (1 - cA D e) * f * (cA D (x : AE D) - 1) := by
    have := congrArg (cA D) hz1
    simp only [RingHom.map_sub, RingHom.map_one, RingHom.map_mul, hfc] at this
    exact this
  have hconj : ν (Units.map (cA D : AE D →* AE D) z) = (ν z)⁻¹ := GlobalTheory.ConjAdjWeil.chi_conj hR z
  obtain ⟨cz, hczdef⟩ : ∃ cz : (AE D)ˣ, cz = Units.map (cA D : AE D →* AE D) z := ⟨_, rfl⟩
  rw [← hczdef] at hconj
  have hcv : (cz : AE D) = cA D (z : AE D) := by rw [hczdef]; rfl
  have hcvi : ((cz⁻¹ : (AE D)ˣ) : AE D) = cA D ((z⁻¹ : (AE D)ˣ) : AE D) := by rw [hczdef, ← map_inv]; rfl
  have hνcz : ν cz = 1 := by
    refine eq_one_of_supp hp hu cz ?_ ?_ ?_
    · rw [hcv, hcz]
      linear_combination (-(cA D (x : AE D) - 1)) * key
    · rw [hcv]; exact finPart_cA_mem iz1
    · rw [hcvi]; exact finPart_cA_mem iz2
  have hνz : ν z = 1 := inv_eq_one.1 (hconj.symm.trans hνcz)
  have hxyz : x = y * z := by rw [hzdef, mul_comm x, mul_inv_cancel_left]
  rw [hxyz, map_mul, hνy, hνz, one_mul]

end GlobalTheory.UnramFromOnePrime

end
