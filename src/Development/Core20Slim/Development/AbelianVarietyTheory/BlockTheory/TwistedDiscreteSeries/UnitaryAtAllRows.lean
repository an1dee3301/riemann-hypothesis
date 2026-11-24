module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Formalism.LocalToGlobal.Divisibility.ClassSum
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
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
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAtAllPlaces

def IsUnitaryRep {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Representation ℂ G H) : Prop :=
  ∀ (g : G) (x y : H), inner ℂ (ρ g x) (ρ g y) = inner ℂ x y

section ClassSum

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ)

def pairAt (x y : S.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (σ (S.bV.repr x i)) * σ (S.gramV i j) * σ (S.bV.repr y j)

def csumAt (f f' : S.Cl → S.V) : ℂ := ∑ c, ((S.wt c : ℂ))⁻¹ * pairAt S σ (f c) (f' c)

def IsUnitaryAtAll {G : Type} [Group G] (r : Representation K G S.Forms) : Prop :=
  ∀ (σ : K →+* ℂ) (g : G) (f f' : S.Forms),
    csumAt S σ (r g f : S.Cl → S.V) (r g f' : S.Cl → S.V) = csumAt S σ (f : S.Cl → S.V) (f' : S.Cl → S.V)

theorem pairAt_smul (a b : K) (x y : S.V) :
    pairAt S σ (a • x) (b • y) = starRingEnd ℂ (σ a) * σ b * pairAt S σ x y := by
  simp only [pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem csumAt_smul (a b : K) (f f' : S.Cl → S.V) :
    csumAt S σ (a • f) (b • f') = starRingEnd ℂ (σ a) * σ b * csumAt S σ f f' := by
  simp only [csumAt, Pi.smul_apply, pairAt_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => by ring

theorem pairAt_eq (h : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) (x y : S.V) : pairAt S σ x y = σ (S.pair x y) := by
  conv_rhs => rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pairAt, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul,
    CSD.gramV, Matrix.of_apply, RingHom.id_apply, starRingEnd_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h, starRingEnd_apply]
  ring

end ClassSum

section Statement

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


variable (A) in
def DefiniteUnitary : Prop :=
  (∀ t : T, IsUnitaryAtAll (A.MtildeCSD t) (A.leftGroupActionRight t)) ∧
    ∀ (i : Fin D.R.m) (t : T), IsUnitaryAtAll (A.MtCSD i t) (A.leftGroupActionLift i t)

end Statement

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAtAllPlaces
