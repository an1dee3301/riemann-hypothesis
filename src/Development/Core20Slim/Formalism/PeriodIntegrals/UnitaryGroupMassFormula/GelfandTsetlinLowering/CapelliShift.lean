module

public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.CapelliEqv
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
public import Formalism.LocalRingCardinality.DataCoeff
public import Development.Core20Slim.Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.CapelliOps
public import Formalism.RealPlaceAnalysis.StatementA
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result

@[expose] public section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem glRel_shift {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) (c : ℂ) :
    Formalism.REAL.GlRel (fun a b => E a b + if a = b then algebraMap ℂ A c else 0) := by
  have key : ∀ (p : Prop) [Decidable p] (y : A),
      (if p then algebraMap ℂ A c else 0) * y = y * (if p then algebraMap ℂ A c else 0) := by
    intro p _ y
    split_ifs
    · exact Algebra.commutes c y
    · simp
  intro i j k l
  simp only
  have h1 := key (i = j) (E k l)
  have h2 := key (k = l) (E i j)
  have h3 := key (i = j) (if k = l then algebraMap ℂ A c else 0)
  calc (E i j + if i = j then algebraMap ℂ A c else 0) * (E k l + if k = l then algebraMap ℂ A c else 0) -
        (E k l + if k = l then algebraMap ℂ A c else 0) * (E i j + if i = j then algebraMap ℂ A c else 0)
      = (E i j * E k l - E k l * E i j)
        + ((if i = j then algebraMap ℂ A c else 0) * E k l - E k l * (if i = j then algebraMap ℂ A c else 0))
        - ((if k = l then algebraMap ℂ A c else 0) * E i j - E i j * (if k = l then algebraMap ℂ A c else 0))
        + ((if i = j then algebraMap ℂ A c else 0) * (if k = l then algebraMap ℂ A c else 0)
          - (if k = l then algebraMap ℂ A c else 0) * (if i = j then algebraMap ℂ A c else 0)) := by
        noncomm_ring
    _ = E i j * E k l - E k l * E i j := by rw [h1, h2, h3]; abel
    _ = (if j = k then E i l else 0) - (if l = i then E k j else 0) := hE i j k l
    _ = _ := by
        by_cases hjk : j = k <;> by_cases hli : l = i
        · subst hjk; subst hli; simp
        · have hil : ¬ i = l := fun h => hli h.symm
          simp [hjk, hli, hil]
        · have hkj : ¬ k = j := fun h => hjk h.symm
          simp [hjk, hli, hkj]
        · simp [hjk, hli]

def capE {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (a b : Fin n) :
    Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
  pol ℂ (Fin.castLE (by omega) a) (Fin.castLE (by omega) b) +
    if a = b then algebraMap ℂ _ (lam.detShift : ℂ) else 0

theorem capE_glRel {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) : Formalism.REAL.GlRel (capE h lam) := by
  have hP := pol_glRel N N
  have hR : Formalism.REAL.GlRel (fun a b : Fin n =>
      (pol ℂ (Fin.castLE (by omega : n ≤ N) a) (Fin.castLE (by omega : n ≤ N) b) :
        Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ))) := by
    intro i j k l
    have := hP (Fin.castLE (by omega) i) (Fin.castLE (by omega) j) (Fin.castLE (by omega) k)
      (Fin.castLE (by omega) l)
    simp only [Fin.castLE_inj] at this
    exact this
  exact glRel_shift _ hR _

theorem capE_apply {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (a b : Fin n) (x : MvPolynomial (Fin N × Fin N) ℂ) :
    capE h lam a b x = pol ℂ (Fin.castLE (by omega) a) (Fin.castLE (by omega) b) x +
      if a = b then (lam.detShift : ℂ) • x else 0 := by
  unfold capE
  split_ifs
  · rw [LinearMap.add_apply, Module.algebraMap_end_apply]
  · simp

end PI.WGL
