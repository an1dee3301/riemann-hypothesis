module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentComponentOfGroupElement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinPartAlgebraMap
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSumFiniteCoordsOfInfinitePartZero
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.List.Pairwise
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitCut

variable {D : D7}

theorem cut_mul {R : Type} [CommRing R] {n : ℕ} (e f : R) (hef : e * f = 0) (M : Matrix (Fin n) (Fin n) R) :
    (e • M + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) * (f • M + (1 - f) • 1) = (e + f) • M + (1 - (e + f)) • 1 := by
  have h1 : e * (1 - f) = e := by rw [mul_sub, mul_one, hef, sub_zero]
  have h2 : (1 - e) * f = f := by rw [sub_mul, one_mul, hef, sub_zero]
  have h3 : (1 - e) * (1 - f) = 1 - (e + f) := by linear_combination hef
  simp only [add_mul, mul_add, smul_mul_smul_comm, Matrix.mul_one, Matrix.one_mul, hef, h1, h2, h3, zero_smul, zero_add]
  rw [add_smul]; abel

theorem mt_mul (V : HSp D) (x y : GA D V) : mt V (x * y) = mt V x * mt V y := by
  show (matHom V (x * y)).1 = (matHom V x).1 * (matHom V y).1
  rw [map_mul, Units.val_mul]


theorem mt_injective (V : HSp D) : Function.Injective (mt V) := by
  intro x y h
  exact Subtype.ext (Units.ext h)


theorem cut_exists (V : HSp D) (g : GA D V) (ε : AE D) (hεε : ε * ε = ε) (hε : cA D ε = ε) :
    ∃ k : GA D V, mt V k = ε • mt V g + (1 - ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  set M := mt V g with hM
  have hinv : M * ((matHom V g)⁻¹).1 = 1 := (matHom V g).mul_inv
  have hinv' : ((matHom V g)⁻¹).1 * M = 1 := (matHom V g).inv_mul
  let K : GL (Fin V.rank) (AE D) := ⟨ε • M + (1 - ε) • 1, ε • ((matHom V g)⁻¹).1 + (1 - ε) • 1,
    GlobalTheory.GfCut.idem_mul ε hεε _ _ hinv, GlobalTheory.GfCut.idem_mul ε hεε _ _ hinv'⟩
  have hgU : Formalism.UG.cT (cA D) M * V.gram.map (incA D) * M = V.gram.map (incA D) :=
    (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2
  have hKU : K ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
    GlobalTheory.GfCut.idem_unitary (cA D) ε hε hεε _ M hgU
  exact ⟨(⟨K, hKU⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram), rfl⟩











theorem idempotent_mul_cut_sub_one_entry {R : Type} [CommRing R] {n : ℕ} (E : R) (hE : E * E = E) (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    E * (E • M + (1 - E) • (1 : Matrix (Fin n) (Fin n) R) - 1) i j = (E • M + (1 - E) • (1 : Matrix (Fin n) (Fin n) R) - 1) i j := by
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * hE

theorem exists_widePullback_of_iteratedLine {R : Type} [CommRing R] {n : ℕ} (t : R) (M : Matrix (Fin n) (Fin n) R)
    (hk : ∀ i j, (1 - t) * (M - 1) i j = 0) : M = t • M + (1 - t) • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  have := hk i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply] at this ⊢
  linear_combination this

theorem mt_list_prod (V : HSp D) {W : Type} (h : W → GA D V) (E : W → AE D)
    (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    (hh : ∀ w, mt V (h w) = E w • M + (1 - E w) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)))
    (horth : ∀ w w', w ≠ w' → E w * E w' = 0) :
    ∀ l : List W, l.Nodup → mt V ((l.map h).prod) = (l.map E).sum • M + (1 - (l.map E).sum) • 1
  | [], _ => by simp
  | w :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, mt_mul, mt_list_prod V h E M hh horth l hl.2, hh, List.map_cons,
      List.sum_cons]
    apply cut_mul
    rw [← List.sum_map_mul_left l E (E w)]
    exact List.sum_eq_zero (List.forall_mem_map.mpr fun y hy =>
      horth w y (fun e => hl.1 (e ▸ hy)))



end GlobalTheory.SplitCut
