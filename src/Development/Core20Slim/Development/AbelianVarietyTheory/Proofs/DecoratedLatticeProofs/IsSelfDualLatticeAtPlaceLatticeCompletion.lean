module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeLocalEqIntegralAlmostAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open NumberField GlobalTheory.FinPl.FrameLat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.IwaPlace.LocSD

variable {D : D7}

theorem exists_idem (v : Pl D) :
    ∃ ε : AE D, cA D ε = ε ∧ ε ∈ intAt D (· = v) ∧ ∀ a, a ∈ idAt D (· = v) → ε * a = a := by
  have hs := GlobalTheory.LatAlmostStd.intSupp_single_mul v (α := 1) (fun w => by rw [map_one]; exact one_mem _)
  rw [mul_one] at hs
  have hp : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.LatAlmostStd.evalV_single_same v 1, fun w hw => GlobalTheory.LatAlmostStd.evalV_single_ne v 1 hw⟩
  refine ⟨pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (1 : D.host.E), ?_,
    ⟨GlobalTheory.FinPl.LatMem.tmul_mem_idAt hs.2 _, AddSubgroup.subset_closure ⟨_, hs.1, 1, rfl⟩⟩,
    fun a ha => ((placeIdem_acts D v _ hp).1 a).1 ha⟩
  change pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (D.sp.cm.sig (1 : D.host.E)) = _
  rw [map_one]

variable {S : HSp D}

theorem hermAt_mul_inc (y : Fin S.rank → AE D) (a : AE D) (s : Fin S.rank → D.host.E) :
    hermAt S y (fun i => a * incA D (s i)) = cA D a * pairing S s y := by
  unfold hermAt pairing FrameLat.row
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.map_mul, RingHom.map_mul, cA_incA, show gA S i j = incA D (S.gram i j) from rfl]
  ring

theorem hermAt_sum_right {m : ℕ} (y : Fin S.rank → AE D) (x : Fin m → Fin S.rank → AE D) :
    hermAt S y (fun i => ∑ l, x l i) = ∑ l, hermAt S y (x l) := by
  unfold hermAt
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin m))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem hermAt_mem_idAt {P : Pl D → Prop} {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D P)
    (x : Fin S.rank → AE D) : hermAt S y x ∈ idAt D P :=
  Ideal.sum_mem _ fun _ _ => Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

variable {L : Lat S}

theorem exists_mul_mem (hL : IsSelfDualC S L) (v : Pl D) :
    ∃ m : ℕ, 0 < m ∧ ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ intAt D (· = v)) → (m : AE D) • y ∈ latV S L (· = v) := by
  have hfull : Submodule.IsFullLattice D.host.E L := by
    haveI : Submodule.IsLattice D.host.E L := hL.1
    refine ⟨?_⟩
    obtain ⟨m, s, s', hs, _, hd⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hL
    apply eq_top_iff.mpr
    intro y _
    have hy : y = ∑ l, (∑ b, (∑ k, star (s' l k) * S.gram k b) * y b) • s l := by
      funext a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have heq : (∑ l, (∑ b, (∑ k, star (s' l k) * S.gram k b) * y b) * s l a) =
          ∑ b, ∑ l, (∑ k, star (s' l k) * S.gram k b) * y b * s l a := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_mul ..
      rw [heq]
      have hterm : ∀ b, (∑ l, (∑ k, star (s' l k) * S.gram k b) * y b * s l a) =
          (if a = b then 1 else 0) * y b := by
        intro b
        calc
          _ = ∑ l, (s l a * ∑ k, star (s' l k) * S.gram k b) * y b := by
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
          _ = _ := by rw [← Finset.sum_mul, hd]
      simp_rw [hterm]
      simp
    rw [hy]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs l))
  obtain ⟨N, hN, -, h⟩ := GlobalTheory.LatAlmostStd.exists_commensurable L hfull
  refine ⟨N.natAbs, Int.natAbs_pos.2 hN, fun y hy => ?_⟩
  have h1 : (N : AE D) • y ∈ latV S L (· = v) := by
    have e : (N : AE D) • y = ∑ i, fun k => y i * incA D ((Pi.single i (N • ((1 : 𝓞 D.host.E) : D.host.E)) :
        Fin S.rank → D.host.E) k) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · rw [Pi.single_eq_same, map_zsmul, show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, RingHom.map_one,
          zsmul_one, Pi.smul_apply, smul_eq_mul, mul_comm]
      · intro i _ hi
        rw [Pi.single_eq_of_ne' hi, RingHom.map_zero, mul_zero]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [e]
    exact sum_mem fun i _ => int_mul_mem (hy i) (h i 1)
  rcases Int.natAbs_eq N with e | e
  · rw [← Int.cast_natCast, ← e]; exact h1
  · have e' : ((N.natAbs : ℕ) : ℤ) = -N := by omega
    rw [← Int.cast_natCast, e', Int.cast_neg, neg_smul]; exact neg_mem h1

theorem isSDAt_latV : ∀ (D : D7) (S : HSp D) (L : Lat S) (v : Pl D), IsSelfDualC S L → IsSDAt S v (latV S L (· = v)) := by
  intro D S L v hL
  refine ⟨fun y hy i => latV_supp hy i, exists_mul_mem hL v, fun y hy => ⟨fun hyL x hx => ?_, fun h => ?_⟩⟩
  · refine ⟨hermAt_mem_idAt hy x, ?_⟩
    obtain ⟨m, s, s', hs, hs', hd⟩ := exists_expansion hL
    have e : x = fun i => ∑ l, (fun l i => pairing S (s' l) x * incA D (s l i)) l i := funext fun i => hd x i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, hermAt_sum_right, map_sum]
    refine sum_mem fun l _ => ?_
    rw [hermAt_mul_inc, RingHom.map_mul]
    exact mul_mem_intAE ((cA_int_iff _).2 (pairing_int hL (hs' l) hx)) (pairing_int hL (hs l) hyL)
  · obtain ⟨ε, hc, hε, hact⟩ := exists_idem v
    refine mem_of_pairing hL hy fun s hs => ?_
    have h1 := (h _ (int_mul_mem hε hs)).2
    rwa [hermAt_mul_inc, hc, hact (pairing S s y) (Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (hy b))] at h1

end GlobalTheory.IwaPlace.LocSD

end
