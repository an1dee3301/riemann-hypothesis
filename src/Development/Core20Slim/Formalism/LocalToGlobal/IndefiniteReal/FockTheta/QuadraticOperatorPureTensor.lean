module

public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
public import Formalism.PeriodIntegrals.HookBound
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HookBound
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix MeasureTheory
open scoped ComplexOrder

namespace Formalism.IndefR.Fock.Der

open Formalism.IndefR.Fock.Sk

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Defs

variable {m n : ℕ}

end Defs

section Steps


end Steps

section Help

variable {ι X : Type} [DecidableEq ι] {Sm : Set (X → ℂ)} {aP aM : ι → (X → ℂ) → (X → ℂ)} {v : X → ℂ}

end Help

section PolHelp

variable {m n : ℕ}


end PolHelp

section Assembly

open Formalism.IndefR.Fock.CCR

variable {m n : ℕ}

section Gen

variable {Sm : Set (Mx D m n → ℂ)} {aP aM : FVar D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)}


end Gen



end Assembly

section FCoordPf

end FCoordPf

section Coords

variable {m n : ℕ}

end Coords

section QuadGen

variable {σ K : Type} [DecidableEq σ] [Fintype K] [DecidableEq K]

end QuadGen

section QuadPf

variable {m n : ℕ}


end QuadPf

section DRhoPf

open Formalism.IndefR.Fock.CCR


end DRhoPf

section HeisFar

open Formalism.IndefR.Fock.DRho

end HeisFar

section OmFar

open Formalism.IndefR.Fock.DRho
open scoped TensorProduct

theorem finPart_mt {V : HSp D} {g : GA D V} (hg : g ∈ GinfC V) : (Formalism.L2.Theta.mt V g).map (finPart D) = 1 := by
  have h0 : finHom V g = 1 := hg
  have h : (finHom V g).1 = 1 := by rw [h0]; rfl
  exact h

end OmFar

end Formalism.IndefR.Fock.Der

end
