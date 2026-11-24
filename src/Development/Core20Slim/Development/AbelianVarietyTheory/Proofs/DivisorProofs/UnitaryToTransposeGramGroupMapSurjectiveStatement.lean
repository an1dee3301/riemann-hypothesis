module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToTransposeGramGroupMapSurjective
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Data.Function
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Matrix Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryToTransposeGramGroupMap_surjective : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • Matrix.reindex e e X.gramᵀ), Function.Surjective (GlobalTheory.SquareAgree.kapX X e hJ) := by
  first | exact @GlobalTheory.SquareAgree.kapX_surjective | exact GlobalTheory.SquareAgree.kapX_surjective | (intros; apply GlobalTheory.SquareAgree.kapX_surjective <;> assumption)
