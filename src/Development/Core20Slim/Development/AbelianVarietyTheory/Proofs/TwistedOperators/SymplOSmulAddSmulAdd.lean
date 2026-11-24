module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubMemOfMkEq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemicharacterSqEqOneOnHalfA
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinDecomp

theorem mem_of_compl_smul {D : D7} {S T : HSp D} {Λ : AddSubgroup (WO S T)} {e : AE D}
    (he : ∀ u ∈ Λ, e • u ∈ Λ) (hc : ∀ u ∈ Λ, cA D e • u ∈ Λ) {y : WO S T} (hy : y ∈ Λ) :
    (1 - e - cA D e) • y ∈ Λ := by
  rw [sub_smul, sub_smul, one_smul]
  exact Λ.sub_mem (Λ.sub_mem hy (he y hy)) (hc y hy)

theorem half_mul_two (D : D7) : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
  norm_num

theorem symplO_split_two {D : D7} {S T : HSp D} {e : AE D} (h1 : e * e = e) (h2 : e * cA D e = 0)
    {x y z : WO S T} (hzx : (1 - e - cA D e) • x = 2 • z) :
    symplO S T x y = symplO S T (e • x) (cA D e • y) + symplO S T (cA D e • x) (e • y) +
      (symplO S T z ((1 - e - cA D e) • y) + symplO S T z ((1 - e - cA D e) • y)) := by
  have hsplit := GlobalTheory.AdForm.HalfASign.symplO_split (S := S) (T := T) h1 h2 x y
  rw [hzx, two_nsmul, GlobalTheory.PlaceModel.symplO_add_left S T] at hsplit
  exact hsplit

theorem symplO_smul_add_smul_add {D : D7} (S T : HSp D) (e : AE D) (x y : WO S T) :
    symplO S T (e • (x + y)) (cA D e • (x + y)) = symplO S T (e • x) (cA D e • x) + symplO S T (e • x) (cA D e • y) +
      (symplO S T (e • y) (cA D e • x) + symplO S T (e • y) (cA D e • y)) := by
  rw [smul_add, smul_add, GlobalTheory.PlaceModel.symplO_add_left S T, GlobalTheory.PlaceModel.symplO_add_right S T,
    GlobalTheory.PlaceModel.symplO_add_right S T]

theorem symplOH_lamE_arg {D : D7} {S T : HSp D} {e : AE D} (h1 : e * e = e) (h2 : e * cA D e = 0)
    {x y z : WO S T} (hzx : (1 - e - cA D e) • x = 2 • z) :
    symplOH S T (e • x) (cA D e • x) + symplOH S T (e • y) (cA D e • y) + symplOH S T x y =
      symplOH S T (e • (x + y)) (cA D e • (x + y)) +
        (symplO S T (cA D e • x) (e • y) + symplO S T z ((1 - e - cA D e) • y)) := by
  unfold symplOH
  rw [symplO_split_two h1 h2 hzx, symplO_smul_add_smul_add S T e x y,
    GlobalTheory.PlaceModel.symplO_skew S T (cA D e • x) (e • y)]
  have hh := half_mul_two D
  generalize algebraMap D.host.F (AF D.host.F) (1 / 2) = h at hh ⊢
  generalize symplO S T (e • x) (cA D e • x) = a1
  generalize symplO S T (e • y) (cA D e • y) = a2
  generalize symplO S T (e • x) (cA D e • y) = a3
  generalize symplO S T (cA D e • x) (e • y) = a4
  generalize symplO S T z ((1 - e - cA D e) • y) = a5
  linear_combination (a4 + a5) * hh

theorem lamE_add_of_lattice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D), e * e = e → e * cA D e = 0 → (∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) → (∀ u ∈ Λ, e • u ∈ Λ) → (∀ u ∈ Λ, cA D e • u ∈ Λ) → (∀ u ∈ Λ, ∃ z ∈ Λ, (1 - e - cA D e) • u = 2 • z) → ∀ x ∈ Λ, ∀ y ∈ Λ, lamE ψ S T e (x + y) = lamE ψ S T e x * lamE ψ S T e y * ψ (symplOH S T x y) := by
  intro D ψ S T Λ e h1 h2 hψ he hc hr x hx y hy
  obtain ⟨z, hz, hzx⟩ := hr x hx
  have key := symplOH_lamE_arg (y := y) h1 h2 hzx
  have k1 : ψ (symplO S T (cA D e • x) (e • y)) = 1 := hψ _ (hc x hx) _ (he y hy)
  have k2 : ψ (symplO S T z ((1 - e - cA D e) • y)) = 1 := hψ _ hz _ (mem_of_compl_smul he hc hy)
  have := congrArg ψ key
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, k1, k2,
    mul_one, mul_one] at this
  unfold lamE
  exact this.symm

end GlobalTheory.FinDecomp
