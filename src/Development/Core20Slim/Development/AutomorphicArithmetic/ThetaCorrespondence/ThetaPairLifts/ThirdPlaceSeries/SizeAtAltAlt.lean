module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeAtHolds
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.Core20Slim.Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Formalism.SharpRestriction.FamCore
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Defs

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
namespace GlobalTheory.BigTop.Fun.SizeProof
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Sizes
variable {D : D7} {L : SizeData₂ D}
end Sizes
section Main
variable {D : D7} {L : SizeData₂ D}
theorem sizeAt_alt : SizeAtAlt :=
  ⟨1, one_pos, fun _ he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hF _ =>
    let ⟨x₀, h⟩ := sizeRows_fam he Fm hF
    ⟨x₀, fun x hx h0 i _ _ => h x hx h0 i⟩⟩⟩
end Main
end GlobalTheory.BigTop.Fun.SizeProof
end
end
