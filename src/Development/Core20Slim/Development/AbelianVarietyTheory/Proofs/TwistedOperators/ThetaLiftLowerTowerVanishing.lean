module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LoweredSignatureVanishing
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignBlockDeterminantOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftCuspFormAutomorphicSmoothModerateGrowth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameExistsSignCompat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.ChainFr GlobalTheory.Size GlobalTheory.Grow GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift
open scoped ENNReal NNReal

namespace GlobalTheory.LowVanishObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Kernel

variable {V W : HSp D} (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (g : GA D V) (h : GA D W)





end Kernel

theorem multT_apply_cusp {W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S) (J : Set (GA D W))
    (χ : GA D W → ℂ) (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M) :
    IsAutFunSm θ W (F v) ∧ IsCuspFun W (F v) := by
  have hT : IsMultMap θ M J χ (PiTensorProduct.lift.symm F) :=
    (GlobalTheory.MultMem.mem_mult_iff D θ W S M J χ _).1 ((mem_multT θ M J χ F).1 hF)
  have hFv : ∀ x, F x = PiTensorProduct.lift (PiTensorProduct.lift.symm F) x := fun x => by
    rw [LinearEquiv.apply_symm_apply]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [hFv, LinearMap.map_smul, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul r (hT.aut x), GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp x)⟩
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add ha.1 hb.1,
      GlobalTheory.MultMem.isCuspFun_add ha.1.toIsAutFun hb.1.toIsAutFun ha.2 hb.2⟩





end GlobalTheory.LowVanishObj

end
