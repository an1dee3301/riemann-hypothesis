module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Formalism.GradedWeylDivisibility.StatementD
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CoefModel

section BaseChange

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] [StarRing K] (φ : K →+* ℂ) (lam : ι → DomWeight n)

theorem fockS_map_int {s : Type} (P : MvPolynomial s ℤ) (g : MvPolynomial s K) :
    fockS (map φ (map (Int.castRingHom K) P)) (map φ g) = φ (fockS (map (Int.castRingHom K) P) g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fockS_eq_sum _ _ (map (Int.castRingHom K) P).support (support_map_subset _ _), fockS, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [coeff_map]

theorem pairK_mapVV_int (G : ι → Matrix (Fin n) (Fin n) K) (x y : VV K lam) (P : MvPolynomial (ι × Fin n × Fin n) ℤ)
    (hx : (x : Pol K ι n) = map (Int.castRingHom K) P) :
    pairK lam (fun τ => (G τ).map φ) (mapVV φ lam x) (mapVV φ lam y) = φ (pairK lam G x y) := by
  have h1 : (map φ).comp (Formalism.GradedWeylDivisibility.blockAct K (n := n) fun τ => (G τ)ᵀ).toRingHom =
      (Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) fun τ => ((G τ).map φ)ᵀ).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro v
      simp [blockAct_X]
  have h2 : map φ (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) y.1) =
      Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((G τ).map φ)ᵀ) (map φ y.1) :=
    congrArg (fun ψ : Pol K ι n →+* Pol ℂ ι n => ψ y.1) h1
  have h3 : φ (gramTw lam G) = gramTw lam fun τ => (G τ).map φ := by
    unfold gramTw
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det]
    rfl
  have h4 : φ (extNorm K lam) = extNorm ℂ lam := by
    unfold extNorm
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← map_extremal φ n (lam τ), ← map_extremal (Int.castRingHom K) n (lam τ), fockS_map_int]
  have h5 := fockS_map_int φ P (Formalism.GradedWeylDivisibility.blockAct K (fun τ => (G τ)ᵀ) y.1)
  rw [← hx] at h5
  rw [pairK_apply, pairK_apply, pairP_apply, pairP_apply, mapVV_coe, mapVV_coe, ← h2, fockL_apply, fockL_apply,
    h5, map_mul, map_div₀, h3, h4]

end BaseChange



end GlobalTheory.CoefModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefModel

variable {D : D7}



end GlobalTheory.CoefModel
