module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRight
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
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
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def IsAwayFn {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (Ψ : Mx D m n → ℂ) : Prop :=
  ∀ x x' : Mx D m n, (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') → x.map (finPart D) = x'.map (finPart D) → Ψ x = Ψ x'

def IsTrivAt (θ : InfFam D) (τ : D.what₂.Tau) (x : G D n) : Prop := compAt θ τ (mat x) = 1

def IsLocFact {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (τ : D.what₂.Tau)
    (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (ι : GR n →* G D n)
    (L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)) : Prop :=
  (∀ y f, IsSch f → IsSch (L y f)) ∧ ∀ (y : GR n) Ψ (hΨ : AwayCls θ τ fr Ψ) f (hf : IsSch f),
    (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (L y f) Ψ

def epsT {m : ℕ} (t : ℝ) (ε : Fin m → Bool) : Fin m → Bool := fun a => if 0 < t then ε a else !ε a

def gramB {m : ℕ} (ε : Fin m → Bool) (b : Bool) (y : Fin m → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => evX (Qb ε b i j) y

def gZf {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * c * (Z * gramB (epsT t ε) true y).trace - Complex.I * c * (Zᴴ * gramB (epsT t ε) false y).trace)

def IsSiegel (Z : Matrix (Fin n) (Fin n) ℂ) : Prop := ((-(Complex.I / 2)) • (Z - Zᴴ)).PosDef

def actZ (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((mR y).toBlocks₁₁ * Z + (mR y).toBlocks₁₂) * ((mR y).toBlocks₂₁ * Z + (mR y).toBlocks₂₂)⁻¹

def jF (e : ℤ) (p q : ℕ) (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (mR y).det ^ e * ((mR y).toBlocks₂₁ * Z + (mR y).toBlocks₂₂).det ^ (-(p : ℤ)) *
    ((mR y).toBlocks₂₁ * Zᴴ + (mR y).toBlocks₂₂).det ^ (-(q : ℤ))

def GZSch : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ), 0 < c → |t| = c → ∀ Z : Matrix (Fin n) (Fin n) ℂ, IsSiegel Z → IsSch (gZf ε t c Z)

def AwayAct : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ x : G D n, IsTrivAt θ τ x →
    ∃ A : (Mx D V.rank n → ℂ) → (Mx D V.rank n → ℂ), ∀ Ψ (hΨ : AwayCls θ τ fr Ψ), AwayCls θ τ fr (A Ψ) ∧
      ∀ f (hf : IsSch f), (ω x ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr f (A Ψ)

def DecompAway : Prop :=
  ∀ (D : D7) (n : ℕ) (θ : InfFam D) (τ : D.what₂.Tau) (ι : GR n →* G D n), IsInfFam θ → IsPlaceEmb θ τ ι → ∀ g : G D n,
    ∃ (x : G D n) (y : GR n), IsTrivAt θ τ x ∧ g = x * ι y ∧ ∀ y' : GR n, x * ι y' = ι y' * x

def LocFact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∃ L, IsLocFact ω τ fr ι L

def GaussLaw : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∃ e : ℤ, ∀ (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ), IsSiegel Z →
      L y (gZf ε (tLoc l τ) (cLoc l τ) Z) = fun u => jF e (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false) y Z *
        gZf ε (tLoc l τ) (cLoc l τ) (actZ y Z) u

end PositivityTheory.Rg.Sw.Glob
