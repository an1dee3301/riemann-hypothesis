module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatLevel


open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem exists_finset_of_nhds_zero {F : Type} [Field F] [NumberField F] (V : Set (Af F)) (hV : IsOpen V)
    (h0 : (0 : Af F) ∈ V) :
    ∃ s : Finset (HeightOneSpectrum (𝓞 F)), ∀ γ ∈ Formalism.MainNotions.StandardLattice.intAf F, (∀ v ∈ s, evalV F v γ = 0) → γ ∈ V := by
  set f := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite with hf
  have hc : Continuous f := (RestrictedProduct.isOpenEmbedding_structureMap
    (fun v => Valued.isOpen_integer _)).continuous
  have hO : IsOpen (f ⁻¹' V) := hV.preimage hc
  have hz : (0 : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) ∈ f ⁻¹' V := h0
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hO _ hz
  refine ⟨I, fun γ hγ hs => ?_⟩
  let x : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F := fun v => ⟨γ v, hγ v⟩
  have hx : x ∈ (I : Set _).pi u := by
    intro v hv
    have h1 : x v = 0 := Subtype.ext (hs v hv)
    rw [h1]
    exact (hu v hv).2
  have := hsub hx
  exact this

end GlobalTheory.LatLevel

namespace GlobalTheory.LatLevel

theorem smul_mem_open_of_vanish : ∀ (D : D7) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop) (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∀ u ∈ latO S T LS LT P, ∃ s : Finset (Pl D), ∀ γ ∈ intAf D.host.F, (∀ v ∈ s, evalV D.host.F v γ = 0) → pairA D.host.F 0 γ • u ∈ U := by
  intro D S T LS LT P U hU u _hu
  letI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have hg : Continuous fun β : Af D.host.F => (pairA D.host.F 0 β) • u := by
    have h1 : Continuous fun β : Af D.host.F => pairA D.host.F 0 β :=
      continuous_const.prodMk continuous_id
    exact h1.smul continuous_const
  obtain ⟨s, hs⟩ := exists_finset_of_nhds_zero _ (hU.preimage hg)
    (by
      show pairA D.host.F 0 0 • u ∈ (U : Set (WO S T))
      have : pairA D.host.F 0 0 = 0 := rfl
      rw [this, zero_smul]
      exact U.zero_mem)
  exact ⟨s, fun γ hγ hv => hs γ hγ hv⟩

end GlobalTheory.LatLevel
