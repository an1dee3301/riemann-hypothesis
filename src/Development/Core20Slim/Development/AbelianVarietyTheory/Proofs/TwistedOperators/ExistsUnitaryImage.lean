module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryQuotient
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockQuadraticActionMapLieBracket
public import Batteries.Classes.RatCast
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Function
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH
open scoped TensorProduct InnerProductSpace Classical Kronecker
open GlobalTheory.Chain.IoLift

noncomputable section

namespace GlobalTheory.Chain.IoLift.UImg

variable {p q : ℕ}

def sumAct (M : GKMod p q) (Y : Type) : Mat p q →ₗ[ℂ] Module.End ℂ (Y →₀ M.V) where
  toFun X := Finsupp.mapRange.linearMap (M.act X)
  map_add' X X' := by
    refine LinearMap.ext fun v => Finsupp.ext fun y => ?_
    simp
  map_smul' c X := by
    refine LinearMap.ext fun v => Finsupp.ext fun y => ?_
    simp

theorem sumAct_apply (M : GKMod p q) (Y : Type) (X : Mat p q) (v : Y →₀ M.V) (y : Y) :
    sumAct M Y X v y = M.act X (v y) := by
  simp [sumAct]

theorem sumAct_single (M : GKMod p q) (Y : Type) (X : Mat p q) (y : Y) (x : M.V) :
    sumAct M Y X (Finsupp.single y x) = Finsupp.single y (M.act X x) := by
  simp [sumAct]

def sumMod (M : GKMod p q) (Y : Type) : GKMod p q where
  V := Y →₀ M.V
  act := sumAct M Y
  lie X X' := by
    refine LinearMap.ext fun v => Finsupp.ext fun y => ?_
    rw [sumAct_apply, M.lie X X']
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Finsupp.sub_apply, sumAct_apply]
  kfin v := by
    induction v using Finsupp.induction_linear with
    | zero => exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun X _ w hw => by
        rw [Submodule.mem_bot] at hw ⊢; rw [hw, map_zero]⟩
    | add f g hf hg =>
      obtain ⟨W, hW, hf, hK⟩ := hf
      obtain ⟨W', hW', hg, hK'⟩ := hg
      refine ⟨W ⊔ W', inferInstance, Submodule.add_mem_sup hf hg, fun X hX w hw => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (hK X hX a ha) (hK' X hX b hb)
    | single y x =>
      obtain ⟨W, hW, hx, hK⟩ := M.kfin x
      refine ⟨W.map (Finsupp.lsingle y), inferInstance, Submodule.mem_map_of_mem hx, ?_⟩
      rintro X hX _ ⟨w, hw, rfl⟩
      rw [Finsupp.lsingle_apply, sumAct_single]
      exact Submodule.mem_map_of_mem (f := Finsupp.lsingle y) (hK X hX w hw)
  wts v := by
    induction v using Finsupp.induction_linear with
    | zero => exact Submodule.zero_mem _
    | add f g hf hg => exact Submodule.add_mem _ hf hg
    | single y x =>
      have h : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) ≤
          (⨆ μ : Ix p q → ℚ, wtSub (sumAct M Y) μ).comap (Finsupp.lsingle y) := by
        refine iSup_le fun μ x hx => ?_
        rw [Submodule.mem_comap]
        refine Submodule.mem_iSup_of_mem μ ?_
        simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
        intro a
        rw [Finsupp.lsingle_apply, sumAct_single, Finsupp.smul_single, ← Finsupp.single_sub, hx a,
          Finsupp.single_zero]
      exact h (M.wts x)

def fockMod (p q r s : ℕ) : GKMod p q where
  V := Pol p q r s
  act := fockAct1 p q r s
  lie X X' := by
    have h : ∀ U : Mat p q, fockAct1 p q r s U = omAct p q r s (U ⊗ₖ (1 : Mat r s)) := fun _ => rfl
    rw [map_sub]
    simp only [h]
    rw [← GlobalTheory.FockLie.omAct_lie, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, map_sub]
  kfin P := ((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 P).1
  wts P := ((GlobalTheory.FockPolGK.pol_locFin_weights p q r s).1 P).2

theorem exists_unitary_image (M : GKMod p q) (Y Z : Type) [AddCommGroup Y] [Module ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] (B : M.V →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z)
    (hB : ∀ (X : Mat p q) P P' y y',
      ⟪B (M.act X P) y, B P' y'⟫_ℂ = ⟪B P y, B (M.act (adjZ X) P') y'⟫_ℂ) :
    ∃ (A : UGKMod p q) (j : A.M.V →ₗ[ℂ] Z) (B' : M.V →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] A.M.V),
      Function.Injective j ∧ (∀ P y, j (B' P y) = B P y) ∧
        Submodule.span ℂ {x | ∃ P y, B' P y = x} = ⊤ ∧
        ∀ X P y, B' (M.act X P) y = A.M.act X (B' P y) := by
  let E : (Y →₀ M.V) →ₗ[ℂ] Z := Finsupp.lsum ℂ fun y => B.flip y
  have hE1 : ∀ y P, E (Finsupp.single y P) = B P y := fun y P => by
    simp [E]
  have hE : ∀ X (x x' : Y →₀ M.V), ⟪E (sumAct M Y X x), E x'⟫_ℂ =
      ⟪E x, E (sumAct M Y (adjZ X) x')⟫_ℂ := by
    intro X x x'
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add (f := _), inner_add_left, hf, hg]
    | single y P =>
      induction x' using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => simp only [map_add (f := _), inner_add_right, hf, hg]
      | single y' P' => simp only [sumAct_single, hE1, hB]
  obtain ⟨A, f, j, hf, hj, hjf, hact⟩ :=
    GlobalTheory.GKQuot.exists_unitary_quotient p q (sumMod M Y) Z E hE
  let g : (Y →₀ M.V) →ₗ[ℂ] A.M.V := f
  have hjg : ∀ y P, j (g (Finsupp.single y P)) = B P y := fun y P => (hjf _).trans (hE1 y P)
  let B' : M.V →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] A.M.V :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun P y => g (Finsupp.single y P))
      (fun P P' y => by rw [Finsupp.single_add, map_add (f := _)])
      (fun c P y => by rw [← Finsupp.smul_single, map_smul, RingHom.id_apply])
      (fun P y y' => hj (by rw [map_add (f := _), hjg, hjg, hjg, map_add (f := _)]))
      (fun c P y => hj (by rw [map_smul, hjg, hjg, map_smulₛₗ]))
  have hB' : ∀ P y, B' P y = g (Finsupp.single y P) := fun _ _ => rfl
  refine ⟨A, j, B', hj, fun P y => hjg y P, ?_, fun X P y => ?_⟩
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨v, rfl⟩ : ∃ v, g v = x := hf x
    induction v using Finsupp.induction_linear with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
    | single y P => exact Submodule.subset_span ⟨P, y, rfl⟩
  · rw [hB', hB', ← sumAct_single]
    exact hact X _

theorem unitaryImage : ∀ p q r s : ℕ, UnitaryImage p q r s :=
  fun p q r s Y Z _ _ _ _ B hB => exists_unitary_image (fockMod p q r s) Y Z B hB

end GlobalTheory.Chain.IoLift.UImg

end
