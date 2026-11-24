module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.Divisibility.LiftLat
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.DivMod.Bootstrap
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColComb

variable {D : D7}

theorem comb_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) (w : WO S T) :
    comb ψ S T c f w = ∑ u ∈ c.support, c u * (ψ (symplOH S T w u) * f (w + u)) := by
  unfold comb
  rw [Finset.sum_apply]
  rfl

theorem comb_comm (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c₁ : WO A S →₀ ℂ) (c₂ : WO S A' →₀ ℂ)
    (G : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    comb ψ S A' c₂ (fun v' => comb ψ A S c₁ (fun u' => G u' v') u) v =
      comb ψ A S c₁ (fun u' => comb ψ S A' c₂ (G u') v) u := by
  simp only [comb_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem biComb_biComb (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c₁ c₁' c₁'' : WO A S →₀ ℂ) (c₂ c₂' c₂'' : WO S A' →₀ ℂ)
    (h₁ : ∀ f, comb ψ A S c₁'' f = comb ψ A S c₁ (comb ψ A S c₁' f))
    (h₂ : ∀ f, comb ψ S A' c₂'' f = comb ψ S A' c₂ (comb ψ S A' c₂' f)) (F : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' c₁ c₂ (biComb ψ A S A' c₁' c₂' F) = biComb ψ A S A' c₁'' c₂'' F := by
  funext u v
  show comb ψ A S c₁ (fun u' => comb ψ S A' c₂ (fun v' => comb ψ A S c₁' (fun u'' => comb ψ S A' c₂' (F u'') v') u') v) u =
    comb ψ A S c₁'' (fun u' => comb ψ S A' c₂'' (F u') v) u
  rw [h₁]
  congr 1
  funext u'
  rw [comb_comm]
  simp only [h₂]

end GlobalTheory.ColComb

open GlobalTheory.ColComb in
theorem GlobalTheory.ColComb.main : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (c : Combs ch.G) (c' c'' : ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), (∀ j, j < D.R.m → ∀ f, comb ch.W.ψ _ _ (c'' j) f = comb ch.W.ψ _ _ (c.1 j) (comb ch.W.ψ _ _ (c' j) f)) → ∀ (C : BiFam ch.G) (u : ColPt ch.G), evT (combC ch.W c (combC ch.W (c', 0) C)) 1 u 0 = evT (combC ch.W (c'', 0) C) 1 u 0 := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ ch _ _
  beta_reduce
  intro c c' c'' hc C u
  unfold evT
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' : 2 * k + 1 < D.R.m := by
    have := Finset.mem_range.mp hk
    omega
  simp only [combC]
  rw [biComb_biComb (h₁ := hc (2 * k) (by omega)) (h₂ := hc (2 * k + 1) hk')]

end
