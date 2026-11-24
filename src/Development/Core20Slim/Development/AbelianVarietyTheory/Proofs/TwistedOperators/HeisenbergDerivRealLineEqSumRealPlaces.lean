module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDirectionalDerivFormulaAndSmooth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGaussEqZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDarbouxOrientedPairTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchLineApply
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedKfin
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
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
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer

namespace GlobalTheory.PlaceSum
open GlobalTheory.OrientedHeis GlobalTheory.FockCompare

theorem hD_finset_sum {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (f : G → ℂ) (hf : Sm ι f) {α : Type} (s : Finset α)
    (u : α → R) : hD ι π om (∑ a ∈ s, u a) f = ∑ a ∈ s, hD ι π om (u a) f := by
  funext w
  rw [Finset.sum_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hD_eq_fderiv ι π om f hf, map_sum, ContinuousLinearMap.sum_apply]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]

theorem deriv_heisO_eq_sum_dRho : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ L : ℝ →+ WO S T, Continuous L →
      (∀ t, (L t).map (finPart D) = 0) →
      (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) f w) 0) =
        ∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f := by
  intro D ψ hψ θ hθ S T f hf L hLc hLf
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e1 : (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) f w) 0) =
      hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (L 1)) f :=
    dLine_eq_hD h hψ (L := L) ⟨hLc, hLf⟩ f
  have e2 : ∀ τ, dRho (heisO ψ S T) θ τ (compAt θ τ (L 1)) f =
      hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (lineAt θ τ (compAt θ τ (L 1)) 1)) f := by
    intro τ
    have hl := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (compAt θ τ (L 1))
    rw [dRho_eq_dLine]
    exact dLine_eq_hD h hψ ⟨hl.1, hl.2.1⟩ f
  have e3 : piW θ T S (L 1) = ∑ τ, piW θ T S (lineAt θ τ (compAt θ τ (L 1)) 1) := by
    funext τ' i j
    simp only [Finset.sum_apply]
    have hc : ∀ τ, piW θ T S (lineAt θ τ (compAt θ τ (L 1)) 1) τ' i j =
        compAt θ τ' (lineAt θ τ (compAt θ τ (L 1)) 1) i j := fun τ => rfl
    simp only [hc]
    rw [Finset.sum_eq_single τ']
    · rw [(GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ' (compAt θ τ' (L 1))).2.2 1 τ', if_pos rfl, Complex.ofReal_one,
        one_smul]
      rfl
    · intro b _ hb
      rw [(GlobalTheory.WeilVacMove.isLineAt_lineAt hθ b (compAt θ b (L 1))).2.2 1 τ', if_neg (Ne.symm hb)]
      rfl
    · intro hn; exact absurd (Finset.mem_univ τ') hn
  rw [e1, e3, hD_finset_sum _ _ _ f (theta_sm h hf)]
  exact Finset.sum_congr rfl fun τ _ => (e2 τ).symm

end GlobalTheory.PlaceSum
