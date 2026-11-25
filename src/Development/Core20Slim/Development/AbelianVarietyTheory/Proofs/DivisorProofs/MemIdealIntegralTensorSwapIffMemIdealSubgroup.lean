module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrincipalCongruenceLevelSubgroupIffIntegralCo
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead.IdealDict

open GlobalTheory.StdRead.CharVal

variable {D : D7}

theorem toE_bijective (D : D7) : Function.Bijective (toE D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).bijective.comp (GlobalTheory.BotFormula.toAfE D).bijective

theorem toE_inc (b : 𝓞 D.host.E) :
    toE D (inc D (b : D.host.E)) = (Formalism.L2.DIV.oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E) := by
  rw [← finQ_incA, toE_finQ]
  rfl

theorem inId_of_mem {𝔪 : Ideal (𝓞 D.host.E)} {y : Formalism.MainNotions.StandardLatticesGL3.AE D} (hy : y ∈ hatId D 𝔪) : InId 𝔪 (toE D y) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, t, ht, rfl⟩ := hy
    have ht' := (toE_int_iff t).2 ht
    have h := Ideal.mul_mem_right (⟨_, ht'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) _
      (Ideal.mem_map_of_mem (Formalism.L2.DIV.oToS D.host.F D.host.E) hb)
    rw [RingHom.map_mul, toE_inc]
    exact ⟨_, h⟩
  | zero => rw [RingHom.map_zero]; exact ⟨zero_mem _, Ideal.zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨h1, h2⟩ := ha
    obtain ⟨h3, h4⟩ := hb
    rw [RingHom.map_add (f := _)]
    exact ⟨add_mem h1 h3, Ideal.add_mem _ h2 h4⟩
  | neg a _ ha =>
    obtain ⟨h1, h2⟩ := ha
    rw [RingHom.map_neg]
    exact ⟨neg_mem h1, Submodule.neg_mem _ h2⟩

theorem exists_of_mem_idS {𝔪 : Ideal (𝓞 D.host.E)} {u : Formalism.L2.Herm.intAf D.host.F D.host.E}
    (hu : u ∈ Ideal.map (Formalism.L2.DIV.oToS D.host.F D.host.E) 𝔪) : ∃ y ∈ hatId D 𝔪, toE D y = u.1 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact ⟨inc D (b : D.host.E), AddSubgroup.subset_closure ⟨b, hb, 1, one_mem _, (mul_one _).symm⟩, toE_inc b⟩
  | zero => exact ⟨0, zero_mem _, RingHom.map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨y, hy, e⟩ := ha
    obtain ⟨z, hz, e'⟩ := hb
    refine ⟨y + z, add_mem hy hz, ?_⟩
    rw [RingHom.map_add (f := _), e, e']
    exact (AddMemClass.coe_add _ a b).symm
  | smul s a _ ha =>
    obtain ⟨y, hy, e⟩ := ha
    obtain ⟨t, ht⟩ := (toE_bijective D).2 s.1
    have htO : t ∈ OhE D := (toE_int_iff t).1 (by rw [ht]; exact s.2)
    refine ⟨t * y, GlobalTheory.FunObj.StdDatum.mul_mem_hatId htO hy, ?_⟩
    have h1 := (toE D).map_mul t y
    rw [e, ht] at h1
    rw [smul_eq_mul]
    exact h1.trans (MulMemClass.coe_mul _ s a).symm

theorem inId_toE_iff : ∀ {D : D7} (𝔪 : Ideal (𝓞 D.host.E)) (y : Formalism.MainNotions.StandardLatticesGL3.AE D), InId 𝔪 (toE D y) ↔ y ∈ hatId D 𝔪 := by
  intro D 𝔪 y
  refine ⟨fun ⟨h, hm⟩ => ?_, inId_of_mem⟩
  obtain ⟨z, hz, e⟩ := exists_of_mem_idS hm
  rwa [← (toE_bijective D).1 e]

end GlobalTheory.StdRead.IdealDict

end
