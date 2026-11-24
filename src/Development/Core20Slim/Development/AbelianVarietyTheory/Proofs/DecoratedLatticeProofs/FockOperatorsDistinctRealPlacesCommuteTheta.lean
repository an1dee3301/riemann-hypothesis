module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
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
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwoPlaceComm

open GlobalTheory.OrientedHeis (theta_add theta_smul theta_dRho)

section Generic

variable {ι X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}





end Generic

section Places

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} (hne : τ ≠ τ')
include hψ hθ hne

theorem dRho_comm_ne (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Datum.dRho (heisO ψ S T) θ τ z (Datum.dRho (heisO ψ S T) θ τ' z' f) =
      Datum.dRho (heisO ψ S T) θ τ' z' (Datum.dRho (heisO ψ S T) θ τ z f) := by
  rw [GlobalTheory.FockIndep.dRho_comm hψ hθ τ z τ' z' hf]
  simp [GlobalTheory.FockIndep.omDir, hne]

theorem dRho_aPlus_ne (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Datum.dRho (heisO ψ S T) θ τ z (aPlus (heisO ψ S T) θ τ' J u f) =
      aPlus (heisO ψ S T) θ τ' J u (Datum.dRho (heisO ψ S T) θ τ z f) := by
  have ht := fun ρ y => theta_dRho hθ hψ ρ y hf
  rw [GlobalTheory.FockIndep.aPlus_eq, GlobalTheory.FockIndep.aPlus_eq,
    GlobalTheory.FockIndep.dRho_smul hψ hθ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))),
    GlobalTheory.FockIndep.dRho_add hψ hθ _ _ (ht _ _) (theta_smul _ (ht _ _)), GlobalTheory.FockIndep.dRho_smul hψ hθ _ _ _ (ht _ _),
    dRho_comm_ne hψ hθ hne _ _ hf, dRho_comm_ne hψ hθ hne _ _ hf]

theorem aPlus_comm_ne (J J' : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z u : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ J z (aPlus (heisO ψ S T) θ τ' J' u f) =
      aPlus (heisO ψ S T) θ τ' J' u (aPlus (heisO ψ S T) θ τ J z f) := by
  have ht := fun ρ y => theta_dRho hθ hψ ρ y hf
  rw [GlobalTheory.FockIndep.aPlus_eq τ J z (aPlus (heisO ψ S T) θ τ' J' u f), dRho_aPlus_ne hψ hθ hne _ _ _ hf,
    dRho_aPlus_ne hψ hθ hne _ _ _ hf, ← GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ _ (ht _ _),
    ← GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)),
    ← GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))), ← GlobalTheory.FockIndep.aPlus_eq]

theorem annih_aPlus_ne (J J' : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z u : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    annih (heisO ψ S T) θ τ J z (aPlus (heisO ψ S T) θ τ' J' u f) =
      aPlus (heisO ψ S T) θ τ' J' u (annih (heisO ψ S T) θ τ J z f) := by
  have ht := fun ρ y => theta_dRho hθ hψ ρ y hf
  rw [annih, annih, dRho_aPlus_ne hψ hθ hne _ _ _ hf, dRho_aPlus_ne hψ hθ hne _ _ _ hf,
    ← GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ _ (ht _ _),
    ← GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _))]

end Places

section Weil

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hW : IsWeilDatumO ψ V W χS χT ω) (hθ : IsInfFam θ)
  {τ τ' : D.what₂.Tau} (hne : τ ≠ τ') {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'))
include hW hθ hne hg




end Weil


end GlobalTheory.TwoPlaceComm

end
