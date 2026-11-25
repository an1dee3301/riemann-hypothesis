module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDrowLemmas
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.LocalRingCardinality.DataCoeff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

abbrev Laurent (k : Type) [Field k] (N : ℕ) : Type := AddMonoidAlgebra k (Fin N → ℤ)

def laurentVar (k : Type) [Field k] (N : ℕ) (a : Fin N) : (Laurent k N)ˣ where
  val := AddMonoidAlgebra.single (Pi.single a 1) 1
  inv := AddMonoidAlgebra.single (-Pi.single a 1) 1
  val_inv := by simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]
  inv_val := by simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]

theorem prod_laurentVar_pow (k : Type) [Field k] (N : ℕ) (d : Fin N → ℕ) :
    (∏ a, ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N) ^ d a) =
      AddMonoidAlgebra.single (fun a => (d a : ℤ)) 1 := by
  have h : ∀ s : Finset (Fin N), (∏ a ∈ s, ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N) ^ d a) =
      AddMonoidAlgebra.single (∑ a ∈ s, d a • (Pi.single a 1 : Fin N → ℤ)) 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [AddMonoidAlgebra.one_def]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      simp [laurentVar, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single]
  rw [h]
  congr 1
  funext b
  simp [Finset.sum_apply, Pi.single_apply]

theorem exists_coeff_of_mem_span {k : Type} [Field k] {N : ℕ} {σ : Type}
    (M : Submodule k (MvPolynomial σ k)) (x : MvPolynomial σ (Laurent k N))
    (hx : x ∈ Submodule.span (Laurent k N)
      (map (algebraMap k (Laurent k N)) '' (M : Set (MvPolynomial σ k)))) :
    ∀ ν : Fin N → ℤ, ∃ h ∈ M, ∀ m, AddMonoidAlgebra.coeff h m = (AddMonoidAlgebra.coeff x m : Laurent k N).coeff ν := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, hh, rfl⟩ := hy
    intro ν
    by_cases hν : ν = 0
    · refine ⟨h, hh, fun m => ?_⟩
      subst hν
      simp [coeff_map, AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.coeff_single]
    · refine ⟨0, zero_mem _, fun m => ?_⟩
      simp [coeff_map, AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hν]
  | zero =>
    intro ν
    exact ⟨0, zero_mem _, fun m => by simp⟩
  | add y z _ _ hy hz =>
    intro ν
    obtain ⟨a, ha, ha'⟩ := hy ν
    obtain ⟨b, hb, hb'⟩ := hz ν
    exact ⟨a + b, add_mem ha hb, fun m => by simp [ha', hb']⟩
  | smul c y _ hy =>
    induction c using AddMonoidAlgebra.induction_linear with
    | zero =>
      intro ν
      exact ⟨0, zero_mem _, fun m => by simp⟩
    | add c₁ c₂ h₁ h₂ =>
      intro ν
      obtain ⟨a, ha, ha'⟩ := h₁ ν
      obtain ⟨b, hb, hb'⟩ := h₂ ν
      refine ⟨a + b, add_mem ha hb, fun m => ?_⟩
      rw [add_smul]
      simp [ha', hb']
    | single u r =>
      intro ν
      obtain ⟨a, ha, ha'⟩ := hy (-u + ν)
      refine ⟨r • a, Submodule.smul_mem _ _ ha, fun m => ?_⟩
      rw [coeff_smul, coeff_smul, smul_eq_mul, smul_eq_mul, ha']
      exact (AddMonoidAlgebra.coeff_single_mul_apply _ _ _ _).symm

theorem weightedHomogeneousComponent_mem_of_isGLSubmodule (k : Type) [Field k] (N : ℕ) (lam : DomWeight N)
    (M : Submodule k (MvPolynomial (Fin N × Fin N) k)) (hM : GlobalTheory.Published.IsGLSubmodule k N lam M)
    (μ : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) k) (hf : f ∈ M) :
    weightedHomogeneousComponent (rowW N N) μ f ∈ M := by
  have h1 := hM (Laurent k N) (diagGL (Laurent k N) N (laurentVar k N)) f hf
  have hdiag : ((diagGL (Laurent k N) N (laurentVar k N) : GL (Fin N) (Laurent k N)) :
      Matrix (Fin N) (Fin N) (Laurent k N)).transpose =
      Matrix.diagonal fun a => ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N) := by
    show (Matrix.diagonal fun a => ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N)).transpose = _
    exact Matrix.diagonal_transpose _
  have h2 : rowAct (Laurent k N) (n := N)
      (Matrix.diagonal fun a => ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N))
      (map (algebraMap k (Laurent k N)) f) ∈ Submodule.span (Laurent k N)
        (map (algebraMap k (Laurent k N)) '' (M : Set (MvPolynomial (Fin N × Fin N) k))) := by
    let u : (Laurent k N)ˣ :=
      Matrix.GeneralLinearGroup.det (diagGL (Laurent k N) N (laurentVar k N)) ^ lam.detShift
    have h3 := Submodule.smul_mem _ ((u⁻¹ : (Laurent k N)ˣ) : Laurent k N) h1
    have e3 : sqAct (Laurent k N) N lam (diagGL (Laurent k N) N (laurentVar k N))
        (map (algebraMap k (Laurent k N)) f) = (u : Laurent k N) • rowAct (Laurent k N) (n := N)
          (Matrix.diagonal fun a => ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N))
          (map (algebraMap k (Laurent k N)) f) := by
      unfold sqAct detPow
      rw [hdiag]
    rw [e3, smul_smul, Units.inv_mul, one_smul] at h3
    exact h3
  obtain ⟨h, hh, hc⟩ := exists_coeff_of_mem_span M _ h2 (fun a => (μ a : ℤ))
  have e : weightedHomogeneousComponent (rowW N N) μ f = h := by
    ext m
    rw [hc, coeff_weightedHomogeneousComponent, ldrow_coeff_rowAct_diag, coeff_map,
      prod_laurentVar_pow, AddMonoidAlgebra.coe_algebraMap]
    have hw : Finsupp.weight (rowW N N) m = μ ↔ (fun a => (rowDeg m a : ℤ)) = fun a => (μ a : ℤ) := by
      constructor
      · intro hw
        funext a
        rw [← ldrow_weight_rowW, hw]
      · intro hw
        funext a
        have := congrFun hw a
        rw [ldrow_weight_rowW]
        exact_mod_cast this
    simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hw]
  rw [e]
  exact hh

end GlobalTheory.Alc
