module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SigV
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.NonUnitalSubring.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FixedUnitNorm

theorem evalAtPlace_singleAtPlace_self (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    evalV F v (singleV F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem evalAtPlace_singleAtPlace_of_ne (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) : evalV F w (singleV F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw

theorem exists_integralAdele_atPlace_component_tmul (D : D7) (v : Pl D) (a : Fv D.host.F v) (ha : a ∈ v.adicCompletionIntegers D.host.F)
    (x : 𝓞 D.host.E) : ∃ y ∈ intAt D (· = v), compAt D v y = a ⊗ₜ[D.host.F] (x : D.host.E) := by
  have hc : ∀ w : Pl D, compAt D w (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E)) =
      evalV D.host.F w (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E) := by
    intro w
    change Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
        (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E))) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    rfl
  refine ⟨pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E), ⟨?_, ?_⟩, ?_⟩
  · rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
    refine ⟨?_, fun w hw => ?_⟩
    · change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
        (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E)) = 0
      rw [Algebra.TensorProduct.map_tmul]
      exact TensorProduct.zero_tmul _ _
    · rw [hc, evalAtPlace_singleAtPlace_of_ne _ v a hw, TensorProduct.zero_tmul]
  · change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E)) ∈ intAE D
    rw [Algebra.TensorProduct.map_tmul]
    refine AddSubgroup.subset_closure ⟨singleV D.host.F v a, fun w => ?_, x, rfl⟩
    by_cases hw : w = v
    · subst hw; rw [evalAtPlace_singleAtPlace_self]; exact ha
    · rw [evalAtPlace_singleAtPlace_of_ne _ v a hw]; exact zero_mem _
  · rw [hc, evalAtPlace_singleAtPlace_self]

theorem exists_intAt_compAt_eq : ∀ (D : D7) (v : Pl D) (z : Fv D.host.F v ⊗[D.host.F] D.host.E), z ∈ intV D v →
    ∃ x ∈ intAt D (· = v), compAt D v x = z := by
  intro D v z hz
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    exact exists_integralAdele_atPlace_component_tmul D v a ha x
  | zero =>
    exact ⟨0, ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩, map_zero _⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨a, ha, hya⟩ := h1
    obtain ⟨b, hb, hzb⟩ := h2
    exact ⟨a + b, GlobalTheory.IwaPlace.SdComap.intAt_add ha hb, by rw [RingHom.map_add (f := _), hya, hzb]⟩
  | neg y _ h =>
    obtain ⟨a, ha, hya⟩ := h
    exact ⟨-a, ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩, by rw [RingHom.map_neg, hya]⟩

end GlobalTheory.FixedUnitNorm

end
