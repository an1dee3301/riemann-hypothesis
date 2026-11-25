module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SmulFinsum
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceS
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

def heisL (w : WO S T) : Module.End ℂ (WO S T → ℂ) where
  toFun := heisO ψ S T w
  map_add' f g := by
    funext x
    simp only [heisO, Pi.add_apply, mul_add]
  map_smul' c f := by
    funext x
    simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem heisL_apply (w : WO S T) (f : WO S T → ℂ) : heisL ψ S T w f = heisO ψ S T w f := rfl

def halfSub (e : AE D) : AddSubgroup (WO S T) where
  carrier := {u | IsHalf e u}
  add_mem' {a b} ha hb := fun i j => by rw [Matrix.add_apply, mul_add, ha i j, hb i j]
  zero_mem' := fun i j => by rw [Matrix.zero_apply, mul_zero]
  neg_mem' {a} ha := fun i j => by rw [Matrix.neg_apply, mul_neg, ha i j]

theorem heisO_heisO (w w' : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w (heisO ψ S T w' f) = ψ (symplOH S T w w') • heisO ψ S T (w + w') f := by
  funext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  rw [symplOH_add_left S T x w w', symplOH_add_right S T x w w', AddChar.map_add_eq_mul,
    AddChar.map_add_eq_mul, add_assoc x w w']
  ring

theorem psi_ne_zero (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem symplO_half {e : AE D} (he : e * cA D e = 0) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    symplO S T x y = 0 := by
  have hz : ∀ a b c d, incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a = 0 := by
    intro a b c d
    rw [← hy c b, ← hx d a, map_mul]
    linear_combination (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) * he
  simp [symplO, hO, hz]

theorem symplOH_half {e : AE D} (he : e * cA D e = 0) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    symplOH S T x y = 0 := by
  rw [symplOH, symplO_half S T he hx hy, mul_zero]

theorem heisL_add_half {e : AE D} (he : e * cA D e = 0) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    heisL ψ S T (x + y) = heisL ψ S T x * heisL ψ S T y := by
  ext1 f
  rw [Module.End.mul_apply, heisL_apply, heisL_apply, heisL_apply, heisO_heisO, symplOH_half S T he hx hy,
    AddChar.map_zero_eq_one, one_smul]

theorem heisL_comm (x y : WO S T) :
    heisL ψ S T x * heisL ψ S T y = ψ (symplO S T x y) • (heisL ψ S T y * heisL ψ S T x) := by
  ext1 f
  simp only [Module.End.mul_apply, LinearMap.smul_apply, heisL_apply]
  rw [heisO_heisO, heisO_heisO, smul_smul, add_comm y x, symplOH_swap S T x y, ← symplOH_two S T x y,
    ← AddChar.map_add_eq_mul, show symplOH S T x y + symplOH S T x y + -symplOH S T x y = symplOH S T x y by abel]

theorem cA_half_orth {e : AE D} (he : e * cA D e = 0) : cA D e * cA D (cA D e) = 0 := by
  rw [cA_cA, mul_comm, he]

end Formalism.IndefR.Fin

end
