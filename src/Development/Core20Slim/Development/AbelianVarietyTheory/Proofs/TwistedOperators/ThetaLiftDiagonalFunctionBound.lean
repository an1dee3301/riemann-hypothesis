module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjThetaKOMulIntegrableOn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate

namespace GlobalTheory.UpArrowApprox

theorem ptF_eq_fock {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : GlobalTheory.Grid.Node D)
    (f : WO S.V T.V → ℂ) (p : GlobalTheory.Grid.Pol S T) :
    GlobalTheory.ChainFr.ptF ψ θ (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel S.M)) (GlobalTheory.ChainFr.Fr.ofModel T.M) f p =
      GlobalTheory.Grid.fock ψ θ true S T f p := by
  have : (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel S.M)).cart = GlobalTheory.Grid.cartS true S :=
    funext fun τ => GlobalTheory.PairLift.cart_frSgn true _ τ
  unfold GlobalTheory.ChainFr.ptF GlobalTheory.Grid.fock
  rw [this]
  rfl

theorem isFinVec_of_isVacF {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : GlobalTheory.Grid.Node D}
    {f : WO S.V T.V → ℂ}
    (h : GlobalTheory.ChainFr.IsVacF ψ θ (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel S.M)) (GlobalTheory.ChainFr.Fr.ofModel T.M) f) :
    GlobalTheory.Grid.IsFinVec ψ θ true S T f :=
  ⟨h.1, fun τ => by have := h.2 τ; rwa [GlobalTheory.PairLift.cart_frSgn] at this⟩

end GlobalTheory.UpArrowApprox

namespace GlobalTheory.UpArrowApprox

end GlobalTheory.UpArrowApprox
