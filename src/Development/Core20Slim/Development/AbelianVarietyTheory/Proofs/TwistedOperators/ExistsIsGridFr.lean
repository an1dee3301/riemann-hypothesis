module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExternalProductOnHermitianSumSmulLeft
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Bool
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareDict

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def datumA (W : G.Weil) {t : T} {i j : ℕ} (Θ : TotT G (routeBig t i j)) :
    WO (G.V (.grid (i + 1) (j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) → ℂ :=
  Θ.sum fun d c => c • box2 (S := negSp (G.V (.grid (i + 1) (j + 1)))) (A := G.V (.grid i (j + 1))) (B := G.V (.grid (i + 1) j))
    d.1.2 (fun y => d.2 (adjM (G.V (.grid (i + 1) (j + 1))) (G.V (.grid (i + 1) j)) y))

def datumB (W : G.Weil) {t : T} {i j : ℕ} (Θ : TotT G (routeSmall t i j)) :
    WO (G.V (.grid i j)) (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) → ℂ :=
  Θ.sum fun d c => c • box2 (S := G.V (.grid i j)) (A := G.V (.grid i (j + 1))) (B := G.V (.grid (i + 1) j))
    d.1.2 (fun y => d.2 (adjM (G.V (.grid i j)) (negSp (G.V (.grid (i + 1) j))) y))

def IsGridFr (W : G.Weil) (X : Node) (A : Fr (G.V X)) : Prop :=
  ∀ τ, A.onb τ = W.onb X τ ∧ A.cart τ = W.cart X τ

theorem exists_isGridFr (W : G.Weil) {X : Node} (hX : X.InRange D.R.m) : ∃ A : Fr (G.V X), IsGridFr W X A := by
  choose ε hε using W.onb_is X hX
  have hu : ∀ τ, IsUnit (W.onb X τ) := fun τ => by
    have h1 : IsUnit ((W.onb X τ)ᴴ * gramAt D (G.V X) τ * W.onb X τ) := by
      rw [(hε τ).1]
      refine ⟨⟨Formalism.REAL.Jm (ε τ), Formalism.REAL.Jm (ε τ), ?_, ?_⟩, rfl⟩ <;>
      · ext a b
        by_cases h : a = b
        · subst h; cases h' : ε τ a <;> simp [Formalism.REAL.Jm, Matrix.mul_apply, Matrix.diagonal_apply, h', Matrix.one_apply]
        · simp [Formalism.REAL.Jm, Matrix.mul_apply, Matrix.diagonal_apply, h, Matrix.one_apply]
    rw [Matrix.isUnit_iff_isUnit_det] at h1 ⊢
    rw [Matrix.det_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  refine ⟨⟨ε, fun τ => (W.onb X τ)⁻¹, fun τ => (Matrix.isUnit_nonsing_inv_iff).2 (hu τ), fun τ => ?_⟩, fun τ => ⟨?_, ?_⟩⟩
  · have hd : IsUnit (W.onb X τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hu τ)
    rw [← (hε τ).1, Matrix.conjTranspose_nonsing_inv]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ (by simpa [Matrix.det_conjTranspose] using hd.star), Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  · have hd : IsUnit (W.onb X τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hu τ)
    show ((W.onb X τ)⁻¹)⁻¹ = W.onb X τ
    exact Matrix.nonsing_inv_nonsing_inv _ hd
  · have hd : IsUnit (W.onb X τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hu τ)
    show ((W.onb X τ)⁻¹)⁻¹ * Formalism.REAL.Jm (ε τ) * (W.onb X τ)⁻¹ = W.cart X τ
    rw [Matrix.nonsing_inv_nonsing_inv _ hd, ← (hε τ).2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

def zact {S X : HSp D} (ω : GlobalTheory.Grid.WRep S X) (z : GA D S →₀ ℂ) (Φ : WO S X → ℂ) : WO S X → ℂ :=
  z.sum fun k c => c • ω (k, 1) Φ

end GlobalTheory.SquareDict
