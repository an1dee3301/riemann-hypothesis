module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.RealRec
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Formalism.FockGram.StatementHerm
public import Formalism.HermitianLattices.StatementLat
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod    ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LineSelfDual

theorem hT_frame (D : D7) (S : HSp D) (u v : S.V) :
    S.hT u v = ∑ i, ∑ j, star (S.frame.equivFun u i) * S.gram i j * S.frame.equivFun v j := by
  conv_lhs => rw [← S.frame.sum_repr u, ← S.frame.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Module.Basis.equivFun_apply, Formalism.BasicNotions.HSpace.gram, starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

noncomputable def selfDualLatticeCoordsInHermitianFrame (D : D7) (S : HSp D) : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E) :=
  S.L0.map (S.frame.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap

theorem frameCoords_mem_selfDualLatticeCoords_iff (D : D7) (S : HSp D) (u : S.V) : S.frame.equivFun u ∈ selfDualLatticeCoordsInHermitianFrame D S ↔ u ∈ S.L0 :=
  ⟨fun ⟨z, hz, e⟩ => S.frame.equivFun.injective e ▸ hz, fun hu => ⟨u, hu, rfl⟩⟩

theorem isSelfDualC_selfDualLatticeCoordsInFrame (D : D7) (S : HSp D) : IsSelfDualC S (selfDualLatticeCoordsInHermitianFrame D S) := by
  refine ⟨⟨S.standardTuple_isLattice.fg.map _, ?_⟩, ?_⟩
  · exact fun _ _ => (LinearIndependent.iff_fractionRing (𝓞 D.host.E) D.host.E).mp
  · intro y
    obtain ⟨v, rfl⟩ := S.frame.equivFun.surjective y
    have h2 : v ∈ S.L0 ↔ ∀ u ∈ S.L0, S.hT u v ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      conv_lhs => rw [← show Formalism.HermitianLatticesTheory.dual S.hT S.L0 = S.L0 from S.baseLattice_isUnimodular]
      simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]
    have h3 : ∀ z : D.host.E, z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔ ∃ b : 𝓞 D.host.E, (b : D.host.E) = z :=
      fun z => Submodule.mem_one.trans ⟨fun ⟨a, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, ha⟩⟩
    rw [frameCoords_mem_selfDualLatticeCoords_iff, h2]
    constructor
    · rintro H _ ⟨u, hu, rfl⟩
      have := (h3 _).1 (H u hu)
      rwa [hT_frame] at this
    · intro H u hu
      rw [h3, hT_frame]
      exact H _ ⟨u, hu, rfl⟩

end GlobalTheory.LineSelfDual
