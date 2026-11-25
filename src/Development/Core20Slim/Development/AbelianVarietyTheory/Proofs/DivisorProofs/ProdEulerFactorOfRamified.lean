module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfTwoMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralSplitPlaceAdelic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelic
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundNonsplitPlaces
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveHeckeLFunctionInvOfTrivialOnMaxReal
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open Formalism.IndefR.Links (ChrEq)

noncomputable section

namespace GlobalTheory.UnrCharZeta

open GlobalTheory.LFun GlobalTheory.PRep
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open Formalism.L2.Host (HChar aboveF)
open GlobalTheory.CMVal (eulerFactor IsHeckeL)

section Seg

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)

end Seg

variable {D : D7}

section Char

variable {E : Type} [Field E] [NumberField E]

theorem loc_inv (ν : HChar E) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) :
    (ν⁻¹).loc w x = (ν.loc w x)⁻¹ := by
  rw [← GlobalTheory.CMVal.finPart_single, ← GlobalTheory.CMVal.finPart_single, GlobalTheory.CMVal.finPart_inv]

theorem unrAt_inv (ν : HChar E) (w : HeightOneSpectrum (𝓞 E)) : (ν⁻¹).UnrAt w ↔ ν.UnrAt w := by
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  rw [loc_inv, inv_eq_one]

theorem val_inv (ν : HChar E) (w : HeightOneSpectrum (𝓞 E)) : (ν⁻¹).val w = (ν.val w)⁻¹ := by
  rw [← GlobalTheory.CMVal.finPart_unifAt, ← GlobalTheory.CMVal.finPart_unifAt, GlobalTheory.CMVal.finPart_inv]

end Char

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Global

section Bottom

open GlobalTheory.FunObj.SqNum (botBig botSmall)

end Bottom

end GlobalTheory.UnrCharZeta

end
