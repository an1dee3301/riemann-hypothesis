module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValueZeroParabolic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousWeilSchrodingerStandardUnnEvalZeroStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorSchrodingerModelIsKFiniteStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
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
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.SiegelSection

theorem fock_mem_degenerate : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → IsSection χ (s0 V n) (fun g : G D n => (ω g Φ).1 0) := by
  intro D n V ψ hψ χ hχ hres θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
  refine ⟨?_, ?_, ?_⟩
  · intro p hp a ha g
    exact GlobalTheory.StdUnn.SiegelLaw.value_zero_parabolic D n V ψ χ θ μ ω hω Φ p hp a ha g
  · exact GlobalTheory.T.continuous_weilSchrodinger_standardUnn_eval_zero D n V ψ hψ χ hχ hres θ hθ μ 𝓕 hμ ω hω Φ
  · have hfin := GlobalTheory.T.fockVector_schrodingerModel_isKFinite D n V ψ hψ χ hχ hres θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
    let L : schwartzA θ V.rank n →ₗ[ℂ] (G D n → ℂ) :=
      { toFun := fun Ψ g => (ω g Ψ).1 0
        map_add' := fun Ψ₁ Ψ₂ => by funext g; simp
        map_smul' := fun c Ψ => by funext g; simp }
    rw [isKFinite_iff]
    refine ⟨(Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ K D n, Ψ = ω k Φ}).map L, inferInstance, ?_⟩
    intro k hk
    have e : (fun g : G D n => (ω (g * k) Φ).1 0) = L (ω k Φ) := by
      funext g; simp [L, map_mul]
    rw [e]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, hk, rfl⟩)

end GlobalTheory.StdUnn.SiegelSection
