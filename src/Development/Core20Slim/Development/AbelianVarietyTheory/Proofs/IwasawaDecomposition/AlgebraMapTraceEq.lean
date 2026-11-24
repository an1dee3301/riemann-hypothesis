module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordinatesFlagVector
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GqPtOfNeZeroIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColReduced
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
public import Formalism.LocalRingCardinality.DataSpaces
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntPair GlobalTheory.IntTerm Formalism.BasicNotions
open Formalism.MainNotions.S (FlagG LieU perpS)

namespace GlobalTheory.RelFlag

section Space

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem hT_eq_form (x y : S.V) : S.hT y x = form (starRingEnd E) S.gram (co S x) (co S y) := by
  rw [hT_eq_sum, form, Matrix.dotProduct_mulVec]; rfl

variable (F : FlagG S r T)

variable {F}

end Space

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.RelFlag
