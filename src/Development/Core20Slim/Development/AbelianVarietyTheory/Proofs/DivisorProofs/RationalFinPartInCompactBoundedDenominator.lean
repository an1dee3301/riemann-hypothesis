module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharAnnihilatorOpenSubgroupFinPartCompact
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntegralOfMemIntAE
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.BoundedDen

theorem continuous_finPart (D : D7) : Continuous (finPart D) := by
  obtain ⟨e, he, hc, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have : (finPart D : AE D → Af D.host.F ⊗[D.host.F] D.host.E) = fun z => (e z).2 := by
    funext z; exact ((he z).2).symm
  rw [this]
  exact continuous_snd.comp hc


set_option maxHeartbeats 1000000 in
theorem bounded_den : ∀ (D : D7) (K : Set (AE D)), IsCompact K → ∃ L : ℕ, 0 < L ∧ ∀ k ∈ K, ∀ x : D.host.E,
    finPart D (incA D x) = finPart D k → IsIntegral ℤ ((L : D.host.E) * x) := by
  intro D K hK
  let U : AddSubgroup (AE D) := (intAE D).comap (finPart D).toAddMonoidHom
  have hU : IsOpen (U : Set (AE D)) :=
    (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage (continuous_finPart D)
  obtain ⟨n, hn⟩ := GlobalTheory.CondBound.exists_small D K hK U hU
  refine ⟨n.factorial, Nat.factorial_pos n, fun k hk x hx => ?_⟩
  have h := hn k hk
  have h2 : finPart D (incA D (((n.factorial : ℕ) : D.host.E) * x)) ∈ intAE D := by
    have e : finPart D (incA D (((n.factorial : ℕ) : D.host.E) * x)) =
        finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F)) * k) := by
      rw [map_mul (incA D), map_mul (finPart D), map_mul (finPart D), hx, GlobalTheory.CondBound.finPart_r]
    rw [e]; exact h
  obtain ⟨y, hy⟩ := GlobalTheory.FinalJoin.CondTest.integral_of_mem_intAE h2
  have e2 : (((n.factorial : ℕ) : D.host.E) * x) = (y : D.host.E) := hy.symm
  rw [e2]
  exact NumberField.RingOfIntegers.isIntegral_coe y

end GlobalTheory.BoundedDen
