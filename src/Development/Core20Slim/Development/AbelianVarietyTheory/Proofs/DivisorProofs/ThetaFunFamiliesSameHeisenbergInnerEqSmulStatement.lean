module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunFamiliesSameHeisenbergInnerEqSmul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOOneOne
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)
open Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.SplitWeil.matrixMeasurableSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFun_families_same_heisenberg_inner_eq_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ι : Type)
    (X Y : ι → Formalism.IndefR.Datum.WO S T → ℂ) (act : Formalism.IndefR.Datum.WO S T → ι → ι)
    (g : Formalism.IndefR.Datum.WO S T → Formalism.IndefR.Datum.WO S T), Function.Surjective g →
    (∀ i, Formalism.IndefR.Datum.IsThetaFunO ψ S T (X i)) → (∀ i, Formalism.IndefR.Datum.IsThetaFunO ψ S T (Y i)) →
    (∀ w i, X (act w i) = Formalism.IndefR.Datum.heisO ψ S T (g w) (X i)) →
    (∀ w i, Y (act w i) = Formalism.IndefR.Datum.heisO ψ S T (g w) (Y i)) →
    ∀ (μ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)), μ.IsAddHaarMeasure →
      MeasureTheory.IsAddFundamentalDomain (Formalism.L2.Theta.ratL T S) 𝓕 μ →
      (∀ i j, ∫ x in 𝓕, X i x * star (X j x) ∂μ = ∫ x in 𝓕, Y i x * star (Y j x) ∂μ) →
      ∃ c : ℂ, ∀ i, X i = c • Y i := by
  first | exact @GlobalTheory.ThetaSchurFam.two_families_scalar | exact GlobalTheory.ThetaSchurFam.two_families_scalar | (intros; apply GlobalTheory.ThetaSchurFam.two_families_scalar <;> assumption)
