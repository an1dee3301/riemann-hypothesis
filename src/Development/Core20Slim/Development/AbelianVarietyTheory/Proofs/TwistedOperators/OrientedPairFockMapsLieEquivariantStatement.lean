module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrientedPairFockMapsLieEquivariant
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orientedPair_fockMaps_lie_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO M X → ℂ) →ₗ[ℂ] Pi), IsCoinvMap θ ω (algF ψ θ ε A B) Pi rf rl p →
  (∀ f, IsFinF ψ θ ε A B f → ∀ τ, ∀ Y ∈ lieAt X τ, ∀ P,
      p (fockF ψ θ ε A B f (GlobalTheory.RealQuot.actT ε A B eS τ Y P)) = rl τ Y (p (fockF ψ θ ε A B f P))) ∧
  (∀ f, IsFinF ψ θ ε A B f → ∀ P ∈ GlobalTheory.RealQuot.coinv ε A B eT, p (fockF ψ θ ε A B f P) = 0) ∧
  ∀ h ∈ GfC X, ∀ f, IsFinF ψ θ ε A B f → ∃ f', IsFinF ψ θ ε A B f' ∧
    ∀ P, rf h (p (fockF ψ θ ε A B f P)) = p (fockF ψ θ ε A B f' P) := by
  first | exact @GlobalTheory.RealQuot.oriented_maps | exact GlobalTheory.RealQuot.oriented_maps | (intros; apply GlobalTheory.RealQuot.oriented_maps <;> assumption)
