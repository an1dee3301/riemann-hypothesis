module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
public import Batteries.Classes.RatCast
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndex
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalarAnnih

open IsDedekindDomain GlobalTheory.Idele
open scoped nonZeroDivisors

theorem exists_compact_annihilator_finiteAdeles_traceChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hc : Continuous ψ)
    (hfin : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)))
    (O : Set (Af F)) (hO : O ∈ nhds (0 : Af F)) : ∃ K : Set (Af F), IsCompact K ∧
      ∀ x : Af F, (∀ t ∈ O, ψ (pairA F 0 (t * x)) = 1) → x ∈ K := by
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F O hO
  obtain ⟨t, ht⟩ := exists_idealOf_eq (GlobalTheory.StdDual.codiff_ne_zero (F := F))
  let c : Af F := algebraMap F (Af F) ((N : F)⁻¹) * (t : Af F)
  refine ⟨(fun a => c * a) '' {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F},
    (GlobalTheory.AdeleCocompact.isCompact_integral F).image (continuous_const.mul continuous_id), ?_⟩
  intro x hx
  have h1 : (N : Af F) * x ∈ adelicIdeal (GlobalTheory.StdDual.codiff F) := by
    rw [GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hc hfin]
    intro α hα
    have := hx _ (hNO α hα)
    rwa [nsmul_eq_mul, mul_assoc, mul_left_comm] at this
  have h2 : (t : Af F) * (((t⁻¹ : (Af F)ˣ) : Af F) * ((N : Af F) * x)) ∈
      adelicIdeal (t • (1 : FractionalIdeal (𝓞 F)⁰ F)) := by
    rw [Units.mul_inv_cancel_left, smul_one_eq, ht]; exact h1
  rw [mul_mem_adelicIdeal_smul, mem_adelicIdeal] at h2
  refine ⟨_, fun v => (mem_localIdeal_one_iff v _).1 (h2 v), ?_⟩
  have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have e : algebraMap F (Af F) ((N : F)⁻¹) * (N : Af F) = 1 := by
    rw [← map_natCast (algebraMap F (Af F)) N, ← map_mul, inv_mul_cancel₀ hN0, map_one]
  simp only [c]
  calc algebraMap F (Af F) ((N : F)⁻¹) * (t : Af F) * (((t⁻¹ : (Af F)ˣ) : Af F) * ((N : Af F) * x))
      = algebraMap F (Af F) ((N : F)⁻¹) * (N : Af F) * x := by
        rw [mul_assoc, Units.mul_inv_cancel_left, mul_assoc]
    _ = x := by rw [e, one_mul]

theorem exists_compact_of_annih : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ O ∈ nhds (0 : Af D.host.F), ∃ K : Set (Af D.host.F), IsCompact K ∧
      ∀ x : Af D.host.F, (∀ t ∈ O, ψ (pairA D.host.F 0 (t * x)) = 1) → x ∈ K :=
  fun D ψ hψ O hO =>
    exists_compact_annihilator_finiteAdeles_traceChar D.host.F ψ hψ.1.1 (GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ) O hO

end GlobalTheory.ScalarAnnih

end
