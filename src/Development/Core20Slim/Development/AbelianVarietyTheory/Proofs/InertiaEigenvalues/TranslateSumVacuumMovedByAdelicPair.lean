module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubIdempotentSmulMemLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.UnitaryVolumePairs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict  
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum  Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

namespace GlobalTheory.AdTh.MovedSum


section Lemmas

open MeasureTheory
open scoped ComplexConjugate

variable {D : D7}




theorem one_sub_smul_mem_latO_pow (V W : HSp D) (LV : Set (Fin V.rank → D.host.E)) (LW : Set (Fin W.rank → D.host.E))
    (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (he : IsIdemSum e P) (x : WO V W)
    (hx : ∀ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∈ PP.asIdeal) →
      ∃ j : ℕ, incA D ((s ^ j : 𝓞 D.host.E) : D.host.E) • x ∈ (latO V W LV LW fun _ => True)) :
    (1 - e) • x ∈ (latO V W LV LW fun _ => True) := by
  obtain ⟨y, hy0, hy, hw⟩ := GlobalTheory.OffIdem.exists_den he
  obtain ⟨j, hj⟩ := hx y hy
  rw [show ((y ^ j : 𝓞 D.host.E) : D.host.E) = (y : D.host.E) ^ j from map_pow (algebraMap (𝓞 D.host.E) D.host.E) y j] at hj
  have h1 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have h2 : (1 - e) * (1 - e) = 1 - e := GlobalTheory.OffIdem.one_sub_mul_self (R := AE D) h1
  have hi : finPart D (1 - e) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, h2])
  set f : AE D := (1 - e) * incA D ((y : D.host.E)⁻¹) with hf
  have hpow : ∀ n : ℕ, ∀ z ∈ (latO V W LV LW fun _ => True), f ^ n • z ∈ (latO V W LV LW fun _ => True) := by
    intro n
    induction n with
    | zero => intro z hz; rwa [pow_zero, one_smul]
    | succ n ih =>
      intro z hz
      rw [pow_succ', mul_smul]
      exact GlobalTheory.LatticeStable.smul_mem_latO D V W LV LW _ _ hw _ (ih z hz)
  have hp : ∀ n : ℕ, (1 - e) * (1 - e) ^ n = 1 - e := by
    intro n
    induction n with
    | zero => rw [pow_zero, mul_one]
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, h2]
  have hyy : incA D ((y : D.host.E)⁻¹) * incA D (y : D.host.E) = 1 := by
    rw [← RingHom.map_mul, inv_mul_cancel₀ hy0, RingHom.map_one]
  have key : (1 - e) * (f ^ j * incA D ((y : D.host.E) ^ j)) = 1 - e := by
    rw [map_pow, ← mul_pow, hf, mul_assoc, hyy, mul_one, hp]
  have := GlobalTheory.LatticeStable.smul_mem_latO D V W LV LW _ _ hi _ (hpow j _ hj)
  rwa [smul_smul, smul_smul, mul_assoc, key] at this


end Lemmas


end GlobalTheory.AdTh.MovedSum
