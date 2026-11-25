module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRs
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPoints
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
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
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section
namespace GlobalTheory.CompanionTheory.WSum

variable {D : D7}

theorem trace_incA_algebraMap_mul (D : D7) (β : D.host.F) (z : AE D) :
    Algebra.trace (AF D.host.F) (AE D) (incA D (algebraMap D.host.F D.host.E β) * z) =
      algebraMap D.host.F (AF D.host.F) β * Algebra.trace (AF D.host.F) (AE D) z := by
  have h : incA D (algebraMap D.host.F D.host.E β) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) β) := by
    show (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E β) =
      (algebraMap D.host.F (AF D.host.F) β) ⊗ₜ[D.host.F] (1 : D.host.E)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [h, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem theta_half_rs {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    {α β : D.host.F} (hβ : β + β = α) (s : ℝ) (t : AE D) (ρ : D.what₂.Tau) :
    θ ρ (infPart D (incA D (algebraMap D.host.F D.host.E β) * (rs σ s * t))) =
      ((1 / 2 * s : ℝ) : ℂ) * θ ρ (infPart D (incA D (algebraMap D.host.F D.host.E α) * t)) := by
  have hi : ∀ e, θ ρ (infPart D (incA D e)) = tauE D ρ e := fun e => (hσ.inf ρ).1 e
  have hs : θ ρ (infPart D (rs σ s)) = (s : ℂ) := hσ.comp _ ρ
  have hb : tauE D ρ (algebraMap D.host.F D.host.E α) =
      tauE D ρ (algebraMap D.host.F D.host.E β) + tauE D ρ (algebraMap D.host.F D.host.E β) := by
    rw [← map_add (f := _), ← map_add (f := _), hβ]
  rw [map_mul (infPart D), map_mul (θ ρ), hi, map_mul (infPart D), map_mul (θ ρ), hs,
    map_mul (infPart D), map_mul (θ ρ), hi, hb]
  push_cast
  ring

theorem psi_halfTr_rs : ∀ (D : D7) (ψ ψ₀ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ₀ (-1) → ∀ α : D.host.F,
    (∀ x, ψ x = ψ₀ (algebraMap D.host.F (AF D.host.F) α * x)) → ∀ (θ : InfFam D)
    (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (t : AE D) (s : ℝ),
    ψ (halfTr (rs σ s * t)) = Complex.exp (2 * Real.pi * Complex.I * ((s * lam θ α t : ℝ) : ℂ)) := by
  intro D ψ ψ₀ h₀ α hψ θ σ hσ t s
  obtain ⟨β, hβ', hβ⟩ : ∃ β : D.host.F, β = α * (1 / 2) ∧ β + β = α := ⟨_, rfl, by ring⟩
  set z' : AE D := incA D (algebraMap D.host.F D.host.E β) * (rs σ s * t) with hz'
  have hR : algebraMap D.host.F (AF D.host.F) α * halfTr (rs σ s * t) =
      Algebra.trace (AF D.host.F) (AE D) z' := by
    rw [hz', trace_incA_algebraMap_mul, hβ', map_mul, mul_assoc]
    rfl
  have hfin : finPart D z' = 0 := by
    have h0 : finPart D (rs σ s) = 0 := hσ.fin _
    rw [hz', map_mul (finPart D), map_mul (finPart D) (rs σ s), h0, zero_mul, mul_zero]
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set R := Algebra.trace (AF D.host.F) (AE D) z' with hRdef
  have h1 : ψ₀ R = psiInf D.host.F ψ₀ (fstA D.host.F R) := by
    unfold psiInf
    rw [← hT]
  have h2 := h₀.2.2 θ hσ.inf (fstA D.host.F R)
  have h3 : ∀ ρ, θ ρ (fstA D.host.F R ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((s * (θ ρ (infPart D (incA D (algebraMap D.host.F D.host.E α) * t))).re : ℝ) : ℂ) := by
    intro ρ
    rw [hRdef, GlobalTheory.PhaseReal.theta_trace θ hσ.inf ρ z', hz', theta_half_rs hσ hβ, Complex.re_ofReal_mul]
    congr 1
    ring
  rw [hψ, hR, h1, h2]
  congr 1
  simp only [h3]
  rw [← Complex.ofReal_sum, ← Finset.mul_sum]
  unfold lam
  push_cast
  ring

end GlobalTheory.CompanionTheory.WSum
