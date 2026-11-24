module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

variable {D : D7}

def congrH {r : ℕ} (a : Matrix (Fin r) (Fin r) D.host.E) (β : HermE D r) : HermE D r :=
  ⟨(a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ * β.1 * a, by
    have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
    have hβ := β.2
    have hm : ∀ (X Y : Matrix (Fin r) (Fin r) D.host.E),
        (X * Y).map (D.sp.cm.sig : D.host.E → D.host.E) =
          X.map (D.sp.cm.sig : D.host.E → D.host.E) * Y.map (D.sp.cm.sig : D.host.E → D.host.E) :=
      fun X Y => Matrix.map_mul (f := (D.sp.cm.sig : D.host.E →+* D.host.E))
    rw [hm, hm, Matrix.transpose_mul, Matrix.transpose_mul, hβ]
    have h2 : ((a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ = a := by
      ext i j; simp [hσ]
    rw [h2, Matrix.mul_assoc]⟩

def IsBlockNF {r : ℕ} (t : ℕ) (β : HermE D r) : Prop :=
  ∃ h : t < r, (∀ i j : Fin r, (t ≤ i.1 ∨ t ≤ j.1) → β.1 i j = 0) ∧
    (β.1.submatrix (Fin.castLE h.le) (Fin.castLE h.le)).det ≠ 0

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
