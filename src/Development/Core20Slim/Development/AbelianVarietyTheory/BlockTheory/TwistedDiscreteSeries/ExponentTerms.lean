module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
open GlobalTheory.SplitWeil GlobalTheory.RootEx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lattices
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def MapsInto (x : Matrix κ ι k) (M' : Submodule 𝒪[k] (ι → k)) (M : Submodule 𝒪[k] (κ → k)) : Prop :=
  ∀ v ∈ M', x *ᵥ v ∈ M


def act (g : GL ι k) (M : Submodule 𝒪[k] (ι → k)) : Submodule 𝒪[k] (ι → k) :=
  M.map ((Matrix.mulVecLin g.val).restrictScalars 𝒪[k])

def stdLat (k : Type) [Field k] [ValuativeRel k] (ι : Type) : Submodule 𝒪[k] (ι → k) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)




end Lattices

section Chain
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}







variable [MeasurableSpace k] [BorelSpace k]



end Chain

end GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
