module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_theta_sum_of_schrodinger : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    @Measurable _ _ (borel _) _ (fun w : (κ → AF F) × (κ → AF F) => GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)) := by
  first | exact @GlobalTheory.ThetaTransformMeas.main | exact GlobalTheory.ThetaTransformMeas.main | (intros; apply GlobalTheory.ThetaTransformMeas.main <;> assumption)
