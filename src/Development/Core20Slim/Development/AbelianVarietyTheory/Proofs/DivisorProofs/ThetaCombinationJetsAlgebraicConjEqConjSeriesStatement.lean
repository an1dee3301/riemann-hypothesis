module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCombinationJetsAlgebraicConjEqConjSeries
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeriesStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfiedStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCombinationJets_algebraic_conj_eq_conjSeries : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (δ t0 : ℂ), Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 →
    ∀ (a b : ℕ), Even (a * b) → ∀ (e0 : VC D a b → ℂ), oddE0 D D.host.ccK δ t0 a b e0 →
    ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
    ∀ (κ : ℂ), Mod1All κ → ∀ (k n : ℕ), 0 < k → ∀ (r : Fin n → Qbar) (s : Fin n → VC D a b),
    (∀ i, k • s i ∈ La D (tor0 D D.host.ccK δ) Ls Lt) → ∀ (ρ' : Qbar →ₐ[ℚ] ℂ) (m : Formalism.L2.Ker.DVar D.what₂.Tau a b →₀ ℕ),
      GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK δ) (s i)
              (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) _ _) (La D (tor0 D D.host.ccK δ) Ls Lt) e0) z) ∈ Qbar ∧
      Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK δ) (s i)
                (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) _ _) (La D (tor0 D D.host.ccK δ) Ls Lt) e0) z)) =
        GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fnConj D Qbar ρ' fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK δ) (s i)
          (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) _ _) (La D (tor0 D D.host.ccK δ) Ls Lt) e0) z) := by
  first | exact @GlobalTheory.ConjJetComb.conj_jet | exact GlobalTheory.ConjJetComb.conj_jet | (intros; apply GlobalTheory.ConjJetComb.conj_jet <;> assumption)
