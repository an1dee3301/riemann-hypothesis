module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaEqSumSchrodingerFunctionPeriodisatioStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
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
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

namespace GlobalTheory.Core.Rk.SchwInj

theorem sch_heisO_extY {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D)
    {ν : Measure (WO A B)} {𝓨 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓨) {f : WO (dblSp A) B → ℂ}
    (hf : IsThetaFunO ψ (dblSp A) B f) (x y : Mx D B.rank A.rank) :
    sch ψ A B ν 𝓨 (heisO ψ (dblSp A) B ((dblDec A).extY B y) f) x =
      ψ (symplO (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y)) * sch ψ A B ν 𝓨 f x :=
  congrFun ((GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) ⟨ν, 𝓨, hν⟩ f hf).2.1 x y) 0

theorem exists_extX_add_extY {D : D7} (A B : HSp D) (w : WO (dblSp A) B) :
    ∃ x y : Mx D B.rank A.rank, w = (dblDec A).extX B x + (dblDec A).extY B y := by
  obtain ⟨⟨x, w₀, y⟩, rfl⟩ := ((dblDec A).coordS B).symm.surjective w
  have hw : w₀ = 0 := Matrix.ext fun _ j => Fin.elim0 j
  subst hw
  refine ⟨x, y, ?_⟩
  show (dblDec A).extX B x + (dblDec A).ext0 B 0 + (dblDec A).extY B y = _
  rw [map_zero, add_zero]

theorem eq_zero_of_sch_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → sch ψ A B ν 𝓨 f = 0 → f = 0 := by
  intro D ψ hψ A B ν 𝓨 hν f hf hs
  funext w
  obtain ⟨x, y, rfl⟩ := exists_extX_add_extY A B w
  have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf ((dblDec A).extY B y)
  have hsum := (GlobalTheory.T.doubledTheta_eq_sum_schrodingerFunction_periodisation D ψ hψ A B ν 𝓨 hν _ hg x).2
  simp only [sch_heisO_extY hψ A B hν hf, hs, Pi.zero_apply, mul_zero] at hsum
  have h0 : ψ (symplOH (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y)) *
      f ((dblDec A).extX B x + (dblDec A).extY B y) = 0 := hsum.unique hasSum_zero
  refine (mul_eq_zero.1 h0).resolve_left fun h => ?_
  have h1 := ψ.map_add_eq_mul (symplOH (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y))
    (-symplOH (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y))
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at h1
  exact one_ne_zero h1

end GlobalTheory.Core.Rk.SchwInj
