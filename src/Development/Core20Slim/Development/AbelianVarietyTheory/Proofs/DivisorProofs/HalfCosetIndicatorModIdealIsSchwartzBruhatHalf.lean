module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
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
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

namespace GlobalTheory.BotSmallDict

set_option synthInstance.maxHeartbeats 400000


set_option maxHeartbeats 1000000 in
theorem cosetFn_isSBHalf : ∀ {D : D7} (S T : HSp D) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    Submodule.IsFullLattice D.host.E LS → Submodule.IsFullLattice D.host.E LT → ∀ (a : Formalism.L2.Theta.AE D), infPart D a = 0 →
    ∀ (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ x : WO S T, IsHalf a x →
      IsSBHalf a (latO S T LS LT fun _ => True) (cosetFn a I x) := by
  intro D S T LS LT hS hT a hinf I hI x _
  obtain ⟨k₁, hk₁, h₁⟩ := GlobalTheory.PlaceVec.exists_nsmul_latO_int (S := S) (T := T) hS.fg hT.fg
  obtain ⟨k₄, hk₄, h₄⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO hS hT (S := S) (T := T)
  obtain ⟨d, hd, hx⟩ := GlobalTheory.PlaceVec.exists_common_nsmul (Formalism.L2.Herm.intAf D.host.F D.host.E).toAddSubgroup
    (fun p : Fin T.rank × Fin S.rank => toEAf D (x p.1 p.2)) fun p => GlobalTheory.PlaceVec.exists_nsmul_mem_int _
  obtain ⟨n₀, hn₀, hnI⟩ : ∃ n₀ : ℕ, 0 < n₀ ∧ ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I :=
    ⟨_, Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h), Ideal.absNorm_mem I⟩
  have hsupp : ∀ t, cosetFn a I x t ≠ 0 →
      IsHalf a t ∧ ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (t i j - x i j)) := fun t ht => by
    unfold cosetFn at ht
    by_contra h
    exact ht (if_neg h)
  refine ⟨fun t ht => (hsupp t ht).1, n₀ * k₁ * (k₄ * d), by positivity, fun u hu hh t => ?_, fun t ht => ?_⟩
  ·
    have hw : ∀ i j, ((k₄ * d) • (k₁ • u.map (toEAf D))) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      fun i j => nsmul_mem (h₁ u hu i j) _
    have hsh : ∀ i j, toEAf D ((t + (n₀ * k₁ * (k₄ * d)) • u : WO S T) i j - x i j) =
        toEAf D (t i j - x i j) + (n₀ : EAf D) * ((k₄ * d) • (k₁ • u.map (toEAf D))) i j := fun i j => by
      rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, RingHom.map_sub,
        RingHom.map_sub, RingHom.map_add, map_nsmul, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    have hH : IsHalf a (t + (n₀ * k₁ * (k₄ * d)) • u) ↔ IsHalf a t := by
      rw [GlobalTheory.PlaceModel.isHalf_iff S T, GlobalTheory.PlaceModel.isHalf_iff S T]
      exact AddSubgroup.add_mem_cancel_right _ (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hh) _)
    have hC : (∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D ((t + (n₀ * k₁ * (k₄ * d)) • u : WO S T) i j - x i j))) ↔
        ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (t i j - x i j)) :=
      ⟨fun H i j => StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.inId_shift hnI (neg_mem (hw i j))
          (by rw [hsh, mul_neg, add_neg_cancel_right]) (H i j),
        fun H i j => StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.inId_shift hnI (hw i j) (hsh i j) (H i j)⟩
    unfold cosetFn
    by_cases hc : IsHalf a t ∧ ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (t i j - x i j))
    · rw [if_pos hc, if_pos ⟨hH.2 hc.1, hC.2 hc.2⟩]
    · rw [if_neg hc, if_neg fun h' => hc ⟨hH.1 h'.1, hC.1 h'.2⟩]
  ·
    obtain ⟨hth, htc⟩ := hsupp t ht
    have hint : IsIntM ((d • t).map (toEAf D)) := fun i j => by
      have e : ((d • t).map (toEAf D)) i j = d • toEAf D (t i j - x i j) + d • toEAf D (x i j) := by
        rw [GlobalTheory.PlaceVec.map_toEAf_nsmul, Matrix.smul_apply, Matrix.map_apply, ← smul_add, RingHom.map_sub, sub_add_cancel]
      rw [e]
      exact add_mem (nsmul_mem (htc i j).1 d) (show d • toEAf D (x i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E from hx (i, j))
    have hinf' : (d • t).map (infPart D) = 0 :=
      GlobalTheory.PlaceVec.half_infPart hinf (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hth) d)
    have h := nsmul_mem (h₄ (d • t) hinf' hint) (n₀ * k₁)
    rw [smul_smul, smul_smul] at h
    rwa [← mul_assoc (n₀ * k₁)]

end GlobalTheory.BotSmallDict
