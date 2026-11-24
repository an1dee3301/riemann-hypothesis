module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsBiSmooth
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.UnimodularTower
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenRealDatumFiniteSumFockProductsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumNonzeroCuspForm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealCentreActsByCharacterOnIsotypicSlicesStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumCentralCharacter
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftFockSumEqSumIteratedLiftsStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftFockSumEqSumIteratedLifts
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutes
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenThetaIsFockVectorBoundedDegree
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmZeroRat
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftPeriodRankZeroFubiniCompactQuotient
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealComponentCentralDefiniteUnitaryEqUnitScalar
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalDefiniteSpaceH
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsPreserveThetaFunctions
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsClosedOfLocallyCompactSpace
public import Formalism.LocalRingCardinality.PosOfIsomEmb
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataLatDefs
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LiftsCart
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.IndefiniteRowSideFullHecke.UnimodularTower
open GlobalTheory.ChainOnto (Com PiLocalization₂)
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSawCompare

variable {D : D7} {u : D.what₂.Word}

theorem defSp_is {V : HSp D} (hs : V.SigOK) (hp : V.IsPosDef) {S : D.what₂.Tau → SPar} (M : DSModel V S) (x : DefSp V)
    (h1 : x.s = cart M) (h2 : x.B = onb M) (h3 : IsSelfDualC V x.L) : x.Is := by
  have hs' : ∀ τ, Formalism.UG.HasSignature (gramAt D V τ) V.rank 0 := fun τ => by
    have := hs (tauE D τ)
    rw [hp (tauE D τ)] at this
    exact this
  have hJ : ∀ τ, Formalism.REAL.Jm (M.ε τ) = 1 := fun τ => by
    have := signs_pos_of_frame_gram_posdef (M.ε τ) (M.fr τ) _ (M.fr_gram τ) (hs' τ)
    unfold Formalism.REAL.Jm; simp [this]
  have hd := fun τ => (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hc : ∀ τ, x.s τ = 1 := fun τ => by rw [h1, cart, hJ, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd τ)]
  refine ⟨hs, Inh.coCpt_of_isDefinite hs fun τ => Or.inl (hp τ), fun τ => ?_, fun τ => Or.inl (hc τ), fun τ => ?_, h3⟩
  · rw [hc]
    exact ⟨by simp, by simp, by simpa using Formalism.IndefR.Fin.Lifts.posDef_of_sig _ (hs' τ)⟩
  · refine ⟨V.rank, fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, by simp [hc]⟩
    rw [h2, onb, ← M.fr_gram τ, hJ, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ (hd τ), Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_nonsing_inv _ (hd τ)]
    simp

abbrev Live (D : D7) (u : D.what₂.Word) : Type := ∀ j, Submodule ℂ (Fn D u j)

variable (W : Live D u) {c : Com D}

section Dbl

variable {σ j : ℕ} {N : Node c u (σ + 1) j} {N' : Node c u σ (j + 1 + 1)} (d : Dbl N N')

end Dbl

section Fin2

variable {j : ℕ} {N : Node c u 0 j} {T : HSp D} {top : RowOn T} (e : Fin2 N top)

end Fin2

variable {W}

section Step

variable {X X' : HSp D} {j : ℕ} {A : ColOn c u X j} {A' : ColOn c u X' (j + 1)} {k : ColStep A A'} {vol : Vol X}

end Step

end GlobalTheory.SeeSawCompare

end
