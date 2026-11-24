module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.AutomorphicForms.QuadraticConj
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

section Complement

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

def IsHyperbolicPair (h : HermitianForm F E W) (v w : W) : Prop :=
  h.toSesq v v = 0 ∧ h.toSesq w w = 0 ∧ h.toSesq v w = 1

def hypComplement (h : HermitianForm F E W) (v w : W) : Submodule E W :=
  LinearMap.ker (h.toSesq v) ⊓ LinearMap.ker (h.toSesq w)

theorem mem_hypComplement {h : HermitianForm F E W} {v w x : W} :
    x ∈ hypComplement h v w ↔ h.toSesq v x = 0 ∧ h.toSesq w x = 0 := by
  simp [hypComplement]

def ComplementForm.Statement (h : HermitianForm F E W) : Prop :=
  ∀ v w : W, IsHyperbolicPair h v w →
    ∃ h' : HermitianForm F E (hypComplement h v w), ∀ x y, h'.toSesq x y = h.toSesq x y

end Complement

namespace GaussianPlane

end GaussianPlane

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
