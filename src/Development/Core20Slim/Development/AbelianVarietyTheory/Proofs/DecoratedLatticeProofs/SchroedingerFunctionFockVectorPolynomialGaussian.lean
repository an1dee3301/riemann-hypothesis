module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnnihilationOperatorSchroedingerFunctionsDoubledStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionLinearThetaFunctionsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicSchwartzSlicePolynomialGaussianOfAnnihilatStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFockSpaceOfPolynomialGaussianSlicesStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhatStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem isThetaFunO_annih_of_std {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {A B : HSp D} {ν : Measure (WO A B)} {𝓨 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓨)
    (τ : D.what₂.Tau)
    (J : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ → Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ)
    (z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) {f : WO (dblSp A) B → ℂ}
    (hf : IsThetaFunO ψ (dblSp A) B f) :
    IsThetaFunO ψ (dblSp A) B (annih (heisO ψ (dblSp A) B) θ τ J z f) := by
  have h1 := GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ z hf
  have h2 := GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ (J z) hf
  have h3 := (GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hψ A B ν 𝓨 hν _ _ h2 h2 Complex.I).2.1
  exact (GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hψ A B ν 𝓨 hν _ _ h1 h3 Complex.I).1

theorem sch_mem_fockA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ (s' : RealMat (dblSp A)) (sB : RealMat B), IsStdInv A μ s' → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) → ∀ l : D.what₂.Tau → ℝ, (∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖) → ∀ f, IsFockVec ψ θ (dblSp A) B s' sB f → sch ψ A B ν 𝓨 f ∈ fockA θ B A.rank l sB := by
  intro D ψ hψ θ hθ A B ν 𝓨 hν μ hμ s' sB hs' hsB l hl f hf
  obtain ⟨hth, N, hN⟩ := hf
  have hS : sch ψ A B ν 𝓨 f ∈ schwartzA θ B.rank A.rank :=
    (GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ hψ θ hθ A B ν 𝓨 hν).1 f hth
  have key : ∀ L : List (D.what₂.Tau × Matrix (Fin B.rank) (Fin A.rank) ℂ),
      IsThetaFunO ψ (dblSp A) B
        (List.foldr (fun (p : D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) g =>
          annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (s' p.1) (sB p.1)) p.2 g) f
          (L.map (fun q => (q.1, q.2 * (dblDec A).qX.map (tauE D q.1))))) ∧
      sch ψ A B ν 𝓨
        (List.foldr (fun (p : D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) g =>
          annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (s' p.1) (sB p.1)) p.2 g) f
          (L.map (fun q => (q.1, q.2 * (dblDec A).qX.map (tauE D q.1))))) =
        L.foldr (fun q g => annS B l sB θ q.1 q.2 g) (sch ψ A B ν 𝓨 f) := by
    intro L
    induction L with
    | nil => exact ⟨hth, rfl⟩
    | cons q L ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨isThetaFunO_annih_of_std hψ hθ hν _ _ _ ih1, ?_⟩
      rw [List.foldr_cons, ← ih2]
      exact GlobalTheory.T.annihilationOperator_schroedingerFunctions_doubledPair D ψ hψ θ hθ A B ν 𝓨 hν μ hμ s' sB hs' hsB l hl _ ih1 q.1 q.2
  have hz : sch ψ A B ν 𝓨 0 = 0 := by
    have h := (GlobalTheory.T.schrodingerFunction_linear_thetaFunctions D ψ hψ A B ν 𝓨 hν f f hth hth 0).2.2.2
    rwa [zero_smul, zero_smul] at h
  refine GlobalTheory.T.mem_fockSpace_of_polynomial_gaussian_slices D θ hθ B A.rank l sB _ hS
    (GlobalTheory.T.adelicSchwartz_slice_polynomial_gaussian_of_annihilated D θ hθ B A.rank l sB hsB N _ hS ?_)
  intro L hL
  rw [← (key L).2, hN _ (by rw [List.length_map, hL]), hz]

end GlobalTheory.StdUnn
