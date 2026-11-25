module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HermSmulOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem locFact_of (hD : Decomp) (hG : OpGen) : LocFact := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  have hop : ∀ y : GR n, ((∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR y = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR y = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR y = mM a)) →
    ∃ L : ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ), (∀ f, IsSch f → IsSch (L f)) ∧
      ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) f (hf : IsSch f),
        (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (L f) Ψ :=
    fun y hy => hG D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y hy
  choose! large₂ hLgS hLg using hop
  have hdec := fun y : GR n => hD n y
  choose y1 y2 y3 y4 hy h1 h2 h3 h4 using hdec
  have g1 : ∀ y, (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR (y1 y) = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR (y1 y) = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR (y1 y) = mM a) := fun y => by
    obtain ⟨t, ht⟩ := h1 y
    exact Or.inl ⟨_, herm_smul_one t, ht⟩
  have g2 : ∀ y, (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR (y2 y) = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR (y2 y) = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR (y2 y) = mM a) := fun y => Or.inr (Or.inl (h2 y))
  have g3 : ∀ y, (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR (y3 y) = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR (y3 y) = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR (y3 y) = mM a) := fun y => Or.inr (Or.inr (h3 y))
  have g4 : ∀ y, (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR (y4 y) = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR (y4 y) = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR (y4 y) = mM a) := fun y => Or.inl (h4 y)
  refine ⟨fun y f => large₂ (y1 y) (large₂ (y2 y) (large₂ (y3 y) (large₂ (y4 y) f))), fun y f hf => ?_, fun y Ψ hΨ f hf => ?_⟩
  · exact hLgS _ (g1 y) _ (hLgS _ (g2 y) _ (hLgS _ (g3 y) _ (hLgS _ (g4 y) _ hf)))
  · have step : ∀ (z : GR n) (hz : (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR z = nU b) ∨
        (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR z = nbar c) ∨
        (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR z = mM a)), ∀ f (hf : IsSch f)
        (h : tens θ τ fr f Ψ ∈ schwartzA θ V.rank n),
        ω (ι z) ⟨tens θ τ fr f Ψ, h⟩ = ⟨tens θ τ fr (large₂ z f) Ψ, hΨ.2 _ (hLgS z hz f hf)⟩ := by
      intro z hz f hf h
      exact Subtype.ext (hLg z hz Ψ hΨ f hf)
    have hprod : ω (ι y) = ω (ι (y1 y)) * ω (ι (y2 y)) * ω (ι (y3 y)) * ω (ι (y4 y)) := by
      conv_lhs => rw [hy y]
      simp only [map_mul]
    rw [hprod]
    simp only [Module.End.mul_apply]
    have s4 := hLgS (y4 y) (g4 y) _ hf
    have s3 := hLgS (y3 y) (g3 y) _ s4
    have s2 := hLgS (y2 y) (g2 y) _ s3
    rw [step (y4 y) (g4 y) _ hf, step (y3 y) (g3 y) _ s4, step (y2 y) (g2 y) _ s3, step (y1 y) (g1 y) _ s2]

theorem locOpEx_of_fact (hF : LocFact) (hA : AwayIn) (hS : SchFP) (hL : LNe) : LocOpEx := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  obtain ⟨L, -, hL2⟩ := hF D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  refine ⟨L, ?_⟩
  intro y Ψ hΨ P
  have hAw : AwayCls θ τ fr Ψ :=
    hA D n V θ l s τ ε fr hC.hθ hC.hs hC.hfr (fun τ' => hL D ψ θ l hC.hψ hC.hθ hC.hl τ') Ψ hΨ
  have hc : 0 < cLoc l τ := by
    have hne := hL D ψ θ l hC.hψ hC.hθ hC.hl τ
    unfold cLoc
    have : 0 < |l τ| := abs_pos.mpr hne
    positivity
  have hf0 : IsSch (fP (cLoc l τ) P) := hS _ _ _ hc P
  rw [phiS_eq' (hAw.2 _ hf0)]
  exact hL2 y Ψ hAw _ hf0

end PositivityTheory.Rg.Sw.Glob
