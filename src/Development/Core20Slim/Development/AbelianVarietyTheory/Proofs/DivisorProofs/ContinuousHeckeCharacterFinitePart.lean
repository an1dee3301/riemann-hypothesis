module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPhaseAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeUChar

open IsDedekindDomain Topology

theorem toFinE_symm_mem_OhE {D : D7} (t : FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (ht : ∀ w : HeightOneSpectrum (𝓞 D.host.E), t w ∈ w.adicCompletionIntegers D.host.E) :
    (GlobalTheory.BotFormula.toFinE D).symm t ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := by
  have hι : ∀ (x : D.host.E) (a : FiniteAdeleRing (𝓞 ℚ) ℚ), (GlobalTheory.BotFormula.toFinE D).toRingHom (x ⊗ₜ[ℚ] a) =
      algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap ℚ D.host.E a := fun x a => by
    show GlobalTheory.LFun.toFinAd ℚ D.host.E (a ⊗ₜ x) = _
    rw [GlobalTheory.LFun.toFinAd_tmul, mul_comm]
  refine GlobalTheory.AdeleBaseChange.mem_int_of_map (ι := (GlobalTheory.BotFormula.toFinE D).toRingHom) hι ?_
  change (GlobalTheory.BotFormula.toFinE D) ((GlobalTheory.BotFormula.toFinE D).symm t) ∈ _
  rw [RingEquiv.apply_symm_apply]
  exact ht

theorem continuous_finChar {D : D7} {N : ℕ} (c : HeckeU D N) : Continuous (finChar c) := by
  refine continuous_of_continuousAt_one (finChar c) ?_
  obtain ⟨m, hm, hc⟩ := c.cont
  have hcont : Continuous (finIdl D) :=
    Continuous.units_map _ (GlobalTheory.DefU.ClassFin.continuous_finAdEquiv.comp (GlobalTheory.Member.continuous_finPart D))
  set W : Set (FiniteAdeleRing (𝓞 D.host.E) D.host.E) :=
    {z | ∀ w : HeightOneSpectrum (𝓞 D.host.E), z w ∈ w.adicCompletionIntegers D.host.E} with hW
  have hWo : IsOpen W := RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  set k : FiniteAdeleRing (𝓞 D.host.E) D.host.E := algebraMap D.host.E _ (m : D.host.E)⁻¹ with hk
  have h1 : Continuous fun x : (AE D)ˣ => ((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) := Units.continuous_val.comp hcont
  have h2 : Continuous fun x : (AE D)ˣ => (((finIdl D x)⁻¹ : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) := Units.continuous_coe_inv.comp hcont
  have h3 : Continuous fun x : (AE D)ˣ => (((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k := (h1.sub continuous_const).mul continuous_const
  set V : Set (AE D)ˣ := ((fun x : (AE D)ˣ => ((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E)) ⁻¹' W ∩
      (fun x : (AE D)ˣ => (((finIdl D x)⁻¹ : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E)) ⁻¹' W ∩
      (fun x : (AE D)ˣ => (((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k) ⁻¹' W) with hVdef
  have hV : IsOpen V :=
    ((hWo.preimage h1).inter (hWo.preimage h2)).inter (hWo.preimage h3)
  have hzero : (0 : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W := fun w => zero_mem _
  have hone : (1 : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W := fun w => one_mem _
  have h1V : (1 : (AE D)ˣ) ∈ V := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show ((finIdl D 1 : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W
      rw [map_one, Units.val_one]; exact hone
    · show (((finIdl D 1)⁻¹ : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) ∈ W
      rw [map_one, inv_one, Units.val_one]; exact hone
    · show (((finIdl D 1 : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k ∈ W
      rw [map_one, Units.val_one, sub_self, zero_mul]; exact hzero
  have hmE : (m : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have key : ∀ x ∈ V, finChar c x = 1 := by
    rintro x ⟨⟨hx1, hx2⟩, hx3⟩
    set u := finIdl D x with hu
    have hy : Formalism.MainNotions.StandardLatticesGL3.IntU D (finY D x) := by
      refine ⟨?_, ?_⟩
      · rw [coe_finY, ← coe_finIdl]
        exact toFinE_symm_mem_OhE _ hx1
      · rw [← map_inv, coe_finY, ← coe_finIdl, map_inv]
        exact toFinE_symm_mem_OhE _ hx2
    have hs : ∃ s ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D, ((finY D x : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 =
        (m : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
      refine ⟨(GlobalTheory.BotFormula.toFinE D).symm ((((u : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
        FiniteAdeleRing (𝓞 D.host.E) D.host.E) - 1) * k), toFinE_symm_mem_OhE _ hx3, ?_⟩
      rw [coe_finY, ← coe_finIdl, ← hu, ← map_natCast (GlobalTheory.BotFormula.toFinE D).symm m, ← map_mul, ← map_one
        (GlobalTheory.BotFormula.toFinE D).symm, ← map_sub]
      congr 1
      have hmk : (m : FiniteAdeleRing (𝓞 D.host.E) D.host.E) * k = 1 := by
        rw [hk, ← map_natCast (algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) m, ← map_mul,
          mul_inv_cancel₀ hmE, map_one]
      rw [mul_comm, mul_assoc, mul_comm k, hmk, mul_one]
    have hf := hc _ hy hs
    exact Circle.ext (by rw [coe_finChar, hf, Units.val_one, Circle.coe_one])
  show Filter.Tendsto (finChar c) (𝓝 1) (𝓝 (finChar c 1))
  rw [map_one]
  exact tendsto_nhds_of_eventually_eq (Filter.eventually_of_mem (hV.mem_nhds h1V) key)

end GlobalTheory.HeckeUChar
