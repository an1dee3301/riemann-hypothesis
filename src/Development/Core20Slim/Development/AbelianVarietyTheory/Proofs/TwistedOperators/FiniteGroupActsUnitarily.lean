module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitaryAtAllRows
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReprMemOfBasisRational
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.ClassSum
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.QuotientMetricDivisors.RatHermLcvTwist
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
open Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Bridge Formalism.L2.Theta
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAtAllPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FiniteGroupUnitary


section ClassSum

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ)

theorem pairAt_eq_of_rat (x y : S.V) (hx : ∀ i, S.bV.repr x i ∈ cmMax K) : pairAt S σ x y = σ (S.pair x y) := by

  have hexp : S.pair x y = ∑ i, ∑ j, star (S.bV.repr x i) * S.gramV i j * S.bV.repr y j := by
    conv_lhs => rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, CSD.gramV, Matrix.of_apply,
      starRingEnd_apply, RingHom.id_apply, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hexp]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pairAt, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_

  have hc : ∀ τ : K →+* ℂ, τ (star (S.bV.repr x i)) = starRingEnd ℂ (τ (S.bV.repr x i)) := hx i
  rw [hc σ]

theorem csumAt_eq_of_rat (f f' : S.Cl → S.V) (hf : S.IsRat f) : csumAt S σ f f' = σ (S.csum f f') := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [csumAt, CSD.csum, map_sum, map_mul, map_inv₀, map_natCast]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pairAt_eq_of_rat S σ (f c) (f' c) (fun i => hf c i)]








end ClassSum

section Presented

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}



end Presented

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levEnv_ch_pow (V : TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) : ∃ n : ℕ, 0 < n ∧ (levEnv V β L).ch q ^ n = 1 := by

  obtain ⟨n, hn, hx⟩ := isOfFinOrder_iff_pow_eq_one.1 (GlobalTheory.HeckeRational.levFn_isOfFinOrder β (Formalism.IndefR.Lev.flagL L)
    (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) q.1.1))
  refine ⟨n, hn, ?_⟩
  have e : (levEnv V β L).ch q = Formalism.L2.DIV.levFn β (Formalism.IndefR.Lev.flagL L)
      (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) q.1.1) := rfl
  rw [e, hx]


end GlobalTheory.FiniteGroupUnitary
