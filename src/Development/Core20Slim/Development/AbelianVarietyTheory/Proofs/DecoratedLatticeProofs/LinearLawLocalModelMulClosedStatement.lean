module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearLawLocalModelMulClosed
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearLaw_localModel_mul_closed : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (S T : HSp D) (ω : Om S T) (μS μT : kˣ →* ℂˣ) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)) (g g' : GA D S) (gk gk' : GL Y' k) (h h' : GA D T) (hk hk' : GL Y k), LawLoc ω μS μT Tm g gk h hk → LawLoc ω μS μT Tm g' gk' h' hk' → LawLoc ω μS μT Tm (g * g') (gk * gk') (h * h') (hk * hk') := by
  first | exact @GlobalTheory.LocOm.LawMul.lawLoc_mul | exact GlobalTheory.LocOm.LawMul.lawLoc_mul | (intros; apply GlobalTheory.LocOm.LawMul.lawLoc_mul <;> assumption)
