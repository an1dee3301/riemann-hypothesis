module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaIntegralIntegrableContinuous
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightTranslate
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteUnitaryCocompact
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnFundamentalDomain
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKOContinuousAndRatInvariant
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
public import Init.Data.Prod
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.DefSourceInt

theorem theta_integral_source_definite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S W : HSp D) (χS χW : (AE D)ˣ →* Circle) (ω : WRep S W) (μ : Measure (GA D S)) (𝓕 : Set (GA D S)) (f : WO S W → ℂ), IsWeil ψ ε S W χS χW ω → (∀ τ, (gramAt D S τ).PosDef) → μ.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 μ → IsThetaFunO ψ (sgn ε S) W f → (∀ h, IntegrableOn (fun g => thetaKO ω g h f) 𝓕 μ) ∧ (Continuous fun h => ∫ g in 𝓕, thetaKO ω g h f ∂μ) ∧ ∀ γ ∈ GQ W, ∀ h, ∫ g in 𝓕, thetaKO ω g (γ * h) f ∂μ = ∫ g in 𝓕, thetaKO ω g h f ∂μ := by
  intro D ψ ε S W χS χW ω μ 𝓕 f hω hpos hμ h𝓕 hf
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hpos
  obtain ⟨hcont, hinv⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ (sgn ε S) W χS χW (WRep.toSgn ε ω) hω f hf
  have hK : ∀ g h, thetaKO ω g h f = thetaKO (WRep.toSgn ε ω) ((ofSgn ε S).symm g) h f := fun _ _ => rfl
  have hKc : Continuous fun p : GA D S × GA D W => thetaKO ω p.1 p.2 f :=
    (hcont.comp (((continuous_ofSgn_symm ε S).comp continuous_fst).prodMk continuous_snd)).congr fun p => (hK p.1 p.2).symm
  have hI : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ W, ∀ g h, thetaKO ω (γ * g) (γ' * h) f = thetaKO ω g h f := by
    intro γ hγ γ' hγ' g h
    rw [hK, hK, map_mul]
    exact hinv _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ ε hγ) γ' hγ' _ _
  have hIS : ∀ γ ∈ GQ S, ∀ g h, thetaKO ω (γ * g) h f = thetaKO ω g h f := fun γ hγ g h => by
    have := hI γ hγ 1 (one_mem _) g h
    rwa [one_mul] at this
  have hIW : ∀ γ ∈ GQ W, ∀ g h, thetaKO ω g (γ * h) f = thetaKO ω g h f := fun γ hγ g h => by
    have := hI 1 (one_mem _) γ hγ g h
    rwa [one_mul] at this
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  refine ⟨fun h => ?_, ?_, fun γ hγ h => ?_⟩
  · exact GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain S μ 𝓕 C hμ h𝓕 hC hcov _
      (hKc.comp (Continuous.prodMk_left h)) (fun γ hγ g => hIS γ hγ g h)
  · exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (GQ S) μ 𝓕 C h𝓕 hC hcov
      (fun h g => thetaKO ω g h f) (hKc.comp continuous_swap) (fun γ hγ h g => hIS γ hγ g h)
  · have e : (fun g => thetaKO ω g (γ * h) f) = fun g => thetaKO ω g h f := funext fun g => hIW γ hγ g h
    exact congrArg (fun F : GA D S → ℂ => ∫ g in 𝓕, F g ∂μ) e

end GlobalTheory.DefSourceInt
