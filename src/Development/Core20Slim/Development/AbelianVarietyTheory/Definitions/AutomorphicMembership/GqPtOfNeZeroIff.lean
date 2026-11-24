module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PrimInIffSubsingleton
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Init.Core
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

section Defs

variable {E : Type} [Field E] [NumberField E] (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)

def Col (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Quot fun Λ Λ' : FrameLats σ J P => ∃ s, InS σ J P s ∧ latMap s Λ.1 = Λ'.1

def Col.lat {σ : E →+* E} {J : Matrix (Fin n) (Fin n) E} {P : Matrix (Fin n) (Fin (r + 1)) E} (c : Col σ J P) :
    Submodule (𝓞 E) (Fin n → E) := (Quot.out c).1

def FrCls (T' : E) (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Quot fun A B : {A // admitted σ J T' g Λ P A} => Move σ J Λ P A.1 B.1

def Term (T' : E) (g : ℕ) (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Σ c : Col σ J P, FrCls σ J T' g c.lat P



variable {σ J} {T' : E} {g : ℕ} {P : Matrix (Fin n) (Fin (r + 1)) E}

namespace Term

variable (t : Term σ J T' g P)

end Term

end Defs

section Basic

variable {E : Type} [Field E] [NumberField E] {σ : E →+* E} {n r g : ℕ} {J : Matrix (Fin n) (Fin n) E}
  {T T' : E} {P A B : Matrix (Fin n) (Fin (r + 1)) E} {Λ : Submodule (𝓞 E) (Fin n → E)}






namespace Term

variable (t : Term σ J T' g P)

variable {t}

variable (t)

end Term

end Basic

section Examples

variable {E : Type} [Field E] [NumberField E]

end Examples

section Spaces

open Formalism.BasicNotions

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]


theorem hT_eq_sum (V : HSpace E) (x y : V.V) :
    V.hT x y = ∑ j, (∑ i, star (V.frame.repr x i) * V.gram i j) * V.frame.repr y j := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    RingHom.id_apply, HSpace.gram, starRingEnd_apply, mul_comm]

end Spaces

section Record

open Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

variable {D} {u u' : D.what₂.Word}

end Record

end GlobalTheory.IntTerm
