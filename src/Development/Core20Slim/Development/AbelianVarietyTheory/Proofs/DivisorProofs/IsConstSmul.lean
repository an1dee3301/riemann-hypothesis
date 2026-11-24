module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotTransfer

variable {D : D7} {T : Type} {A A' WW : HSp D}

theorem ker_smul (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T) (κ : ℂ)
    (P : PolF D WW.rank A.rank) (h : GA D WW) (g : GA D A) :
    X.ker ψ θ t (κ • P) h g = κ * X.ker ψ θ t P h g := by
  simp only [Tri.ker, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]

theorem isConst_smul {X : Tri T A A' WW} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {c : T → ℂ}
    (h : X.IsConst ψ θ c) {κ : ℂ} (hκ : κ ≠ 0) : X.IsConst ψ θ fun t => κ * c t := by
  obtain ⟨⟨t₁, h₁⟩, P, P', H⟩ := h
  refine ⟨⟨t₁, mul_ne_zero hκ h₁⟩, κ • P, P', fun t => ⟨fun g => ⟨?_, ((H t).1 g).2⟩, (H t).2.1, fun g => ?_⟩⟩
  · have := ((H t).1 g).1.const_mul κ
    have e : X.ker ψ θ t (κ • P) g = fun x => κ * X.ker ψ θ t P g x := funext fun x => ker_smul X ψ θ t κ P g x
    rw [IntegrableOn, e]
    exact this
  · have e : X.I ψ θ t (κ • P) g = κ * X.I ψ θ t P g := by
      simp only [Tri.I, ker_smul, MeasureTheory.integral_const_mul]
    rw [e, (H t).2.2 g, mul_assoc]

end GlobalTheory.BotTransfer
