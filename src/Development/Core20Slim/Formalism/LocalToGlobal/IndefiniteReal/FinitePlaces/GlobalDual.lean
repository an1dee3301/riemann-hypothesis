module

public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.GlobalDualOfBasis
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatSmulSingle
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharDual
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PairingRankOneMemInverseDifferent
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.StdCharExists
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Fin.PDA

open Formalism.IndefR.Fin Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem globalDual (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (h : ∀ c ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, betaO S T γ (rk1 S T c s t) ∈ invDiff D.host.F) :
    γ ∈ Submodule.span ℤ {M | ∃ c ∈ D.host.AA, ∃ s ∈ ΛS, ∃ t ∈ ΛT, M = rk1 S T c s t} :=
  globalDual_of_basis S T hT (selfDual_basis S hS) γ h

end Formalism.IndefR.Fin.PDA

end
