module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameMatrixWeilPairActionLeftInvStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizerStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegralStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentComponentOfGroupElementStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingIdempotentPatchInFrameStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameIdempotentCutMatrixMemStabiliserReductionStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalProjectionEqOfIdempotentPatchStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjIdempotentConjFixedStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOneStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhds
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.SuppLevO

variable {D : D7}

theorem proj_eq_one_of_finHom (V : HSp D) (h : GA D V) (hh : h ∈ GinfC V) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v h = 1 := by
  rw [← GlobalTheory.AdelicU.projFinLoc_projFin]
  have : GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram h = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact congrArg Units.val hh
  rw [this, map_one]

theorem proj_finPartG (V : HSp D) (g : GA D V) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v (GlobalTheory.LevelNbhd.finPartG V g) = GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g := by
  have h := proj_eq_one_of_finHom V _ (GlobalTheory.LevelNbhd.inv_finPartG_mul_mem_GinfC V g) v
  rw [map_mul, map_inv, inv_mul_eq_one] at h
  exact h

theorem finE_finPartG (V : HSp D) (g : GA D V) : Lev.finE V (GlobalTheory.LevelNbhd.finPartG V g) = Lev.finE V g := by
  show (Formalism.UG.bc _) (finHom V _) = (Formalism.UG.bc _) (finHom V g)
  rw [GlobalTheory.LevelNbhd.finHom_finPartG]





end GlobalTheory.SuppLevO
