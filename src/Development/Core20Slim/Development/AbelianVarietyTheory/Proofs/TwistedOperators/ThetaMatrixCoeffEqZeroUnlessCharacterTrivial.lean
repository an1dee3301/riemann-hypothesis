module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionsSquareIntegrableHeisenbergUnitary
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoeffVanish

theorem matrixCoeff_eq_zero : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν →
    ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
    ∃ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) ∧ ∀ ξ : WO V W, ∀ u ∈ U, u.map (infPart D) = 0 →
      ψ (symplO V W ξ u) ≠ 1 → ∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν = 0 := by
  intro D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG'

  obtain ⟨U₁, hU₁, hGfix⟩ := hG.level
  obtain ⟨U₂, hU₂, hG'fix⟩ := hG'.level
  refine ⟨U₁ ⊓ U₂, ?_, ?_⟩
  · rw [AddSubgroup.coe_inf]
    exact hU₁.inter hU₂
  intro ξ u hu hfin hψu
  obtain ⟨hcomp, -, hkeep, hunit, -⟩ := GlobalTheory.ThetaSquare.heisUnitary (V := V) (W := W) hψ
  have hGu : heisO ψ V W u G = G := hGfix u hu.1 hfin
  have hG'u : heisO ψ V W u G' = G' := hG'fix u hu.2 hfin

  have hswap : symplOH V W u ξ = -symplOH V W ξ u := GlobalTheory.MixModel.symplOH_skew V W ξ u
  have hmove : heisO ψ V W u (heisO ψ V W ξ G) = ψ (-symplO V W ξ u) • heisO ψ V W ξ G := by
    have hξG : heisO ψ V W ξ G = ψ (symplOH V W ξ u) • heisO ψ V W (ξ + u) G := by
      have h := hcomp ξ u G
      rwa [hGu] at h
    rw [hcomp u ξ G, add_comm u ξ, hξG, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hswap, GlobalTheory.ThetaSquare.symplO_eq]
    ring

  set c : ℂ := ψ (-symplO V W ξ u) with hc
  have hI := hunit ν 𝓕 hν h𝓕 u (heisO ψ V W ξ G) G' (hkeep ξ G hG) hG'
  rw [hmove, hG'u] at hI
  unfold GlobalTheory.Ker.ipO at hI
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, starRingEnd_apply] at hI
  rw [MeasureTheory.integral_const_mul] at hI
  have hc1 : c ≠ 1 := by
    intro h1
    apply hψu
    have hprod : ψ (symplO V W ξ u) * c = 1 := by
      rw [hc, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rwa [h1, mul_one] at hprod
  have hsub : (c - 1) * ∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν = 0 := by
    rw [sub_mul, one_mul, hI, sub_self]
  rcases mul_eq_zero.mp hsub with h | h
  · exact absurd (sub_eq_zero.mp h) hc1
  · exact h

end GlobalTheory.CoeffVanish

end
