module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Formalism.GradedWeylDivisibility.FinalC
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsRelationsDivPowBaseChangStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceRowOperatorPowerDualWeylHighestWeightStatement
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.StatementA
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Int.CharZero
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section
namespace GlobalTheory.Alc

theorem hcVal_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {N : ℕ} (μ : Fin N → R) (k : ℕ) :
    hcVal S (fun i => φ (μ i)) k = φ (hcVal R μ k) := by
  have hM : hcMat S (fun i => φ (μ i)) = (hcMat R μ).map φ := by
    ext i l
    simp only [hcMat, shift, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  have hP : (hcMat S (fun i => φ (μ i))) ^ k = ((hcMat R μ) ^ k).map φ := by
    rw [hM]
    exact (map_pow (RingHom.mapMatrix φ) (hcMat R μ) k).symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hcVal, hP, Matrix.map_apply, map_sum]

theorem gel_dualWeyl_int (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν) (j : ℕ) (f : MvPolynomial (Fin N × Fin N) ℤ)
    (hf : f ∈ dualWeyl ℤ N N ν) : gel ℤ N N j f = hcVal ℤ (fun i => (ν i : ℤ)) j • f := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
  rw [(GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange ℤ N N).2.2 ℚ (Int.castRingHom ℚ) j f,
    GlobalTheory.T.traceRowOperatorPower_dualWeyl_highestWeight N ν hν j _ (dualWeylMap ℤ ℚ (Int.castRingHom ℚ) N N ν f hf),
    smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  congr 2
  rw [← hcVal_map]
  simp

theorem gel_dualWeyl_field : ∀ (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ j : ℕ,
    ∀ f ∈ dualWeyl k N N ν, gel k N N j f = hcVal k (fun i => (ν i : k)) j • f := by
  intro k _ N ν hν j f hf
  rw [standardMonomialSpanDomain k N N ν] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hg
    have hb : bideterminant k sz hsz I = map (Int.castRingHom k) (bideterminant ℤ sz hsz I) := by
      simp only [bideterminant, initMinor, map_prod]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [RingHom.map_det]
      congr 1
      ext p q
      simp
    have hmem : bideterminant ℤ sz hsz I ∈ dualWeyl ℤ N N ν := hsh ▸ bidetMem ℤ N N K sz hsz I
    rw [hb, ← (GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange ℤ N N).2.2 k (Int.castRingHom k) j, gel_dualWeyl_int N ν hν j _ hmem,
      smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
    congr 2
    rw [← hcVal_map]
    simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

end GlobalTheory.Alc
