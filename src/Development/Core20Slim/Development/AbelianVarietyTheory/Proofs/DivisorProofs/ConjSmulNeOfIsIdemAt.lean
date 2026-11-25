module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaTildeHeckeCharSplitMulSignOfNormFormula
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinPartMulIncAMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderSmulOfFix
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Group.Action
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum

theorem conj_smul_ne_of_isIdemAt {D : D7} {e : Formalism.L2.Theta.AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e P) : D.host.conj • P.asIdeal ≠ P.asIdeal := by
  intro h
  have hc := GlobalTheory.EtaProduct.cA_of_fixed (GlobalTheory.HeckeDetChar.isPlIdem he) h
  have h0 : e = 0 := by
    have := he.1.2.1
    rw [hc, he.1.1] at this
    exact this
  apply P.ne_bot
  refine eq_bot_iff.2 fun x hx => ?_
  by_contra hx0
  have := (he.2 x hx0).1 hx
  rw [h0, zero_mul, map_zero] at this
  exact this (zero_mem _)

theorem condE_isCoprime_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L),
    IsCoprime (condE P) (D.host.conj • condE P) := by
  intro D T L P
  have hF : ∀ I : Ideal (𝓞 D.host.E), (D.host.conj • I).under (𝓞 D.host.F) = I.under (𝓞 D.host.F) :=
    GlobalTheory.PlaceOverPair.under_smul_of_fix D.host.conj
      (fun x => (D.host.conjE_mem_hostF_iff _).1 x.2)
  unfold GlobalTheory.FunObj.SqNum.condE
  rw [Finset.smul_prod']
  refine IsCoprime.prod_left fun v hv => IsCoprime.prod_right fun v' hv' => ?_
  rw [smul_pow']
  refine IsCoprime.pow ?_
  rw [Ideal.isCoprime_iff_sup_eq]
  have hm : (D.host.conj • (P.w v').asIdeal).IsMaximal := by
    have := (P.w v').isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => (P.w v').ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  refine Ideal.IsMaximal.coprime_of_ne (P.w v).isMaximal hm fun heq => ?_
  have hvv : v = v' := by
    have a := congrArg HeightOneSpectrum.asIdeal (P.under_w hv)
    have b := congrArg HeightOneSpectrum.asIdeal (P.under_w hv')
    refine HeightOneSpectrum.ext ?_
    rw [← a, ← b]
    show Ideal.under _ _ = Ideal.under _ _
    rw [heq, hF]
  subst hvv
  obtain ⟨e, he⟩ := P.w_split v hv
  exact conj_smul_ne_of_isIdemAt he heq.symm

end GlobalTheory.FunObj.StdDatum

end
