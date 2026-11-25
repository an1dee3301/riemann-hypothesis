module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
public import Development.Core20Slim.Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LatCoordA
public import Development.Core20Slim.Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LatCoordB
public import Formalism.PairingDivisors.PairingDivisorProofs.ValAdd
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem lossLe_mul_wild_jets {D : D7} (w : PlL D) {x y : ℂ} {a b : ℝ}
    (hx : LossLe w x a) (hy : LossLe w y b) : LossLe w (x * y) (a + b) := by
  obtain ⟨s, hs, hs'⟩ := hx
  obtain ⟨t, ht, ht'⟩ := hy
  refine ⟨s * t, by rw [map_mul, hs, ht], ?_⟩
  rcases hs' with h0 | h1
  · left; simp [h0]
  rcases ht' with h0 | h2
  · left; simp [h0]
  by_cases hs0 : s = 0
  · left; simp [hs0]
  by_cases ht0 : t = 0
  · left; simp [ht0]
  right
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w s t hs0 ht0]
  push_cast
  linarith
private theorem lossLe_add {D : D7} (w : PlL D) {x y : ℂ} {a : ℝ}
    (hx : LossLe w x a) (hy : LossLe w y a) : LossLe w (x + y) a := by
  obtain ⟨s, hs, hs'⟩ := hx
  obtain ⟨t, ht, ht'⟩ := hy
  refine ⟨s + t, by rw [map_add (f := _), hs, ht], ?_⟩
  by_cases hs0 : s = 0
  · subst hs0; simpa using ht'
  by_cases ht0 : t = 0
  · subst ht0; simpa using hs'
  by_cases hst : s + t = 0
  · left; exact hst
  right
  have h1 : -a ≤ (vw w s : ℝ) := hs'.resolve_left hs0
  have h2 : -a ≤ (vw w t : ℝ) := ht'.resolve_left ht0
  have h3 := Formalism.PairingDivisionLocalBalance.vw_add w s t hs0 ht0 hst
  have h4 : ((min (vw w s) (vw w t) : ℤ) : ℝ) ≤ (vw w (s + t) : ℝ) := by exact_mod_cast h3
  rw [Int.cast_min] at h4
  exact le_trans (le_min h1 h2) h4
private theorem lossLe_finset_sum {D : D7} (w : PlL D) {ι : Type*} (S : Finset ι) (g : ι → ℂ) {a : ℝ}
    (hg : ∀ i ∈ S, LossLe w (g i) a) : LossLe w (∑ i ∈ S, g i) a := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp, Or.inl rfl⟩
  | insert j S hj ih =>
    rw [Finset.sum_insert hj]
    exact lossLe_add w (hg j (Finset.mem_insert_self j S))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

theorem UpperTheory.WildA.matLat :
    ∀ (D : D7) {n n' : ℕ} (lam : D.what₂.Tau → DomWeight n) (lam' : D.what₂.Tau → DomWeight n') (w : PlL D) (l : ℕ), l.Prime →
      (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)),
      Formalism.MainNotions.TaylorLogMetric.EqAt D l Λ (Formalism.MainNotions.StandardLatticesGL3.stdL D n) → Formalism.MainNotions.TaylorLogMetric.EqAt D l Λ' (Formalism.MainNotions.StandardLatticesGL3.stdL D n') →
      ∀ (f : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (c : ℝ), (∀ i j, LossLe w ((bVV ℂ lam').repr (f (bVV ℂ lam j)) i) c) →
      ∀ (a : ℝ) (v : VV ℂ lam), InLat lam w a Λ v → InLat lam' w (a + c) Λ' (f v) := by
  intro D n n' lam lam' w l hl hlw Λ Λ' hΛ hΛ' f c hf a v hv
  apply UpperTheory.WildA.latCoordB D lam' w l hl hlw Λ' hΛ' (a + c) (f v)
  intro i
  have hv' := UpperTheory.WildA.latCoordA D lam w l hl hlw Λ hΛ a v hv
  have hsum := (bVV ℂ lam).sum_repr v
  have hrepr : (bVV ℂ lam').repr (f v) i =
      ∑ j, (bVV ℂ lam).repr v j * (bVV ℂ lam').repr (f (bVV ℂ lam j)) i := by
    calc (bVV ℂ lam').repr (f v) i
        = (bVV ℂ lam').repr (f (∑ j, (bVV ℂ lam).repr v j • bVV ℂ lam j)) i := by rw [hsum]
      _ = _ := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_sum, Finset.sum_apply']
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [hrepr]
  exact lossLe_finset_sum w _ _ fun j _ => lossLe_mul_wild_jets w (hv' j) (hf i j)
