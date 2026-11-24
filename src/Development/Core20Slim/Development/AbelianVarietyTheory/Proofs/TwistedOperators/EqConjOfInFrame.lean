module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToPairMul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSource
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaximalCompactActsOnFockVectorsBySubstitution
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSizesNR
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Subst

variable {D : D7}

def fockSubAll {m n : ℕ} (pS pT : D.what₂.Tau → ℕ) (κS : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (κT : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) : MvPolynomial (FVar D m n) ℂ →ₐ[ℂ] MvPolynomial (FVar D m n) ℂ :=
  MvPolynomial.aeval fun y : FVar D m n =>
    ∑ i, ∑ j, MvPolynomial.C (if (y.2.1.val < pT y.1 ↔ y.2.2.val < pS y.1) then κT y.1 i y.2.1 * (κS y.1)⁻¹ y.2.2 j
      else (starRingEnd ℂ) (κT y.1 i y.2.1 * (κS y.1)⁻¹ y.2.2 j)) * MvPolynomial.X (y.1, i, j)

end Subst

section Points

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def ptTop (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (n : ℕ) : GA D (G.V (.top n)) :=
  if h : n < D.R.m then (kappa W g).1 ⟨n, h⟩ else if h' : n = D.R.m then h' ▸ kappaTop W g else 1

def ptGrid (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (i : ℕ) : GA D (G.V (.grid i D.R.m)) :=
  if h : i < D.R.m + 1 then (kappa W g).2 ⟨i, h⟩ else 1

theorem ptTop_lt (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) {n : ℕ} (h : n < D.R.m) :
    ptTop W g n = (kappa W g).1 ⟨n, h⟩ := by
  simp only [ptTop, dif_pos h]

theorem ptTop_m (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) : ptTop W g D.R.m = kappaTop W g := by
  simp only [ptTop, lt_irrefl, dif_neg (lt_irrefl _), not_false_eq_true]
  rfl

theorem ptGrid_le (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) {i : ℕ} (h : i < D.R.m + 1) :
    ptGrid W g i = (kappa W g).2 ⟨i, h⟩ := by
  simp only [ptGrid, dif_pos h]

end Points

section Scal

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sizes} (P : ι → Entries S)

def rowScal (j : Fin S.m) (g : Gc ι S) : ℂ :=
  ((detChar (S.nR j.castSucc) (fun τ => (P τ).e j - (S.nR j.succ / 2 : ℕ)) ((rowComp S g) j.castSucc) *
    detChar (S.nR j.succ) (fun τ => -(P τ).e j + (S.nR j.castSucc / 2 : ℕ)) ((rowComp S g) j.succ) : ℂˣ) : ℂ)

def colScal (i : Fin S.m) (g : Gc ι S) : ℂ :=
  ((detChar (S.nC i.castSucc) (fun τ => (P τ).c i.rev - ((S.nC i.succ + 1) / 2 : ℕ)) (g.2 i.castSucc) *
    detChar (S.nC i.succ) (fun τ => -(P τ).c i.rev + ((S.nC i.castSucc + 1) / 2 : ℕ)) (g.2 i.succ) : ℂˣ) : ℂ)

end Scal

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Frame

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def topFrame (W : G.Weil) (τ : D.what₂.Tau) : Matrix (Fin (G.V (.top D.R.m)).rank) (Fin (G.V (.top D.R.m)).rank) ℂ :=
  Matrix.of fun a k =>
    Sum.elim (fun b : Fin ((rowSizes D).nC D.R.m) =>
        ((frameMat _ _ G.sp.topDec.ι).map (tauE D τ) * W.onb (.grid D.R.m D.R.m) τ) a (Fin.cast (rank_gridM G le_rfl).symm b))
      (fun _ : Fin 1 => (G.sp.topDec.a.map (tauE D τ)) a 0)
      ((finSumFinEquiv.trans (finCongr (rowSizes D).nC_succ)).symm (Fin.cast (rank_top G le_rfl) k))

end Frame

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section More

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem ptTop_mem (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (n : ℕ) : ptTop W g n ∈ GinfC (G.V (.top n)) := by
  unfold ptTop
  split_ifs with h h'
  · exact kappa_fst_mem W g _
  · subst h'; exact kappaTop_mem W g
  · exact one_mem _

theorem ptGrid_mem (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (i : ℕ) : ptGrid W g i ∈ GinfC (G.V (.grid i D.R.m)) := by
  unfold ptGrid
  split_ifs with h
  · exact kappa_snd_mem W g _
  · exact one_mem _

theorem isKMat_cast {a b : ℕ} (h : a = b) (u : Matrix.unitaryGroup (Fin b) ℂ) {p : ℕ} (hp : p = a ∨ p = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat p ((u : Matrix (Fin b) (Fin b) ℂ).submatrix (Fin.cast h) (Fin.cast h)) := by
  subst h
  refine ⟨by simpa using u.2, fun i j hij => absurd ?_ hij⟩
  rcases hp with rfl | rfl
  · exact iff_of_true i.2 j.2
  · exact iff_of_false (Nat.not_lt_zero _) (Nat.not_lt_zero _)

theorem trCol_injective (G : GridData L sc) (j : Fin D.R.m) : Function.Injective (trCol G j) :=
  MvPolynomial.rename_injective _ fun x y h => by
    simp only [Prod.mk.injEq, Fin.cast_inj] at h
    exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)

theorem trRow_injective (G : GridData L sc) (i : Fin D.R.m) : Function.Injective (trRow G i) :=
  MvPolynomial.rename_injective _ fun x y h => by
    simp only [Prod.mk.injEq, Fin.cast_inj] at h
    exact Prod.ext h.1 (Prod.ext h.2.2 h.2.1)

theorem eq_conj_of_inFrame {n : ℕ} {B M K : Matrix (Fin n) (Fin n) ℂ} (hB : IsUnit B.det) (h : B⁻¹ * M * B = K) :
    M = B * K * B⁻¹ := by
  rw [← h]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul]

end More

end GlobalTheory.RowReal
