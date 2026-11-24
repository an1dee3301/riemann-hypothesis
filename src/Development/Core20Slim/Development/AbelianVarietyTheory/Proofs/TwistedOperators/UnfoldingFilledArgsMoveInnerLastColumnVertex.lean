module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Ext
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Defs.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

noncomputable section
namespace GlobalTheory.TopLevelInv

theorem fill_moveVertex : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (j : ℕ) (hj : j + 1 < Γ.m) (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k)
    (x x' : ColArgs Γ) (y : RowArgs Γ) (e e' : Vars Γ),
    (∀ l, l ≠ j → l ≠ j + 1 → downMap hs x' e' l = downMap hs x e l) →
    downMap hs x' e' j = (g⁻¹).val * downMap hs x e j →
    downMap hs x' e' (j + 1) = downMap hs x e (j + 1) * g.val →
    Γ.moveArgs .one (Pi.mulSingle (Γ.m, j + 1) g) (fill hs x y e) = fill hs x' y e' := by
  intro k _ _ _ _ _ _ Γ hs j hj g x x' y e e' hrest hj0 hj1
  funext b
  cases b with
  | theta i l =>
    by_cases hi : i = Γ.m
    · subst hi
      rw [moveArgs_theta, fill_theta, fill_theta, transpose_transpose]
      by_cases hl : l = j
      · subst hl
        have h1 : (Pi.mulSingle (Γ.m, l + 1) g : Γ.VertexGroup) (Γ.m, l) = 1 :=
          Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h) _
        rw [h1, Pi.mulSingle_eq_same, Units.val_one, Matrix.mul_one, hj0]
      · by_cases hl' : l = j + 1
        · subst hl'
          have h1 : (Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) (Γ.m, j + 1 + 1) = 1 :=
            Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h) _
          rw [h1, Pi.mulSingle_eq_same, inv_one, Units.val_one, Matrix.one_mul, hj1]
        · have h1 : (Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) (Γ.m, l) = 1 :=
            Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
          have h2 : (Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) (Γ.m, l + 1) = 1 :=
            Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
          simp only [h1, h2, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one, hrest l hl hl']
    · simp [fill, Grid.moveArgs, hi]
  | ex i l =>
    by_cases hl : l = Γ.m
    · subst hl
      have h1 : (Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) (i, Γ.m) = 1 :=
        Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
      have h2 : (Pi.mulSingle (Γ.m, j + 1) g : Γ.VertexGroup) (i + 1, Γ.m) = 1 :=
        Pi.mulSingle_eq_of_ne (by intro h; simp [Prod.ext_iff] at h; omega) _
      simp only [Grid.moveArgs, Edge.src, Edge.tgt, fill_ex, h1, h2, map_one, inv_one, Units.val_one,
        Matrix.one_mul, Matrix.mul_one]
    · simp [fill, Grid.moveArgs, hl]

end GlobalTheory.TopLevelInv

end
