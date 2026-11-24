module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLawsStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergDerivativeThetaFunctionLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensity
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Multiset.ZeroCons
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.FockAlg

section Generic

variable {ι X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

theorem foldr_mem (hA : ∀ i f, P f → P (A i f)) {f : X → ℂ} (hf : P f) (l : List ι) :
    P (l.foldr (fun i g => A i g) f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact hA i _ ih

theorem foldr_perm (hA : ∀ i f, P f → P (A i f)) (hc : ∀ i j f, P f → A i (A j f) = A j (A i f))
    {f : X → ℂ} (hf : P f) {l l' : List ι} (h : l.Perm l') :
    l.foldr (fun i g => A i g) f = l'.foldr (fun i g => A i g) f := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.foldr_cons, ih]
  | swap x y l => simp only [List.foldr_cons]; exact hc _ _ _ (foldr_mem hA hf l)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem pure_monomial (f : X → ℂ) (k : ι →₀ ℕ) (c : ℂ) :
    pureTensorL A f (MvPolynomial.monomial k c) = c • opPow A k f := by
  have hm : MvPolynomial.monomial k c = c • MvPolynomial.basisMonomials ι ℂ k := by
    rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul]
  unfold pureTensorL
  rw [Module.Basis.constr_basis]

theorem pure_one (f : X → ℂ) : pureTensorL A f 1 = f := by
  rw [← map_one MvPolynomial.C, MvPolynomial.C_apply, pure_monomial, one_smul]
  simp [opPow]

theorem pure_mem (hadd : ∀ f f', P f → P f' → P (f + f')) (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (hA : ∀ i f, P f → P (A i f)) {f : X → ℂ} (hf : P f) (Q : MvPolynomial ι ℂ) : P (pureTensorL A f Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [pure_monomial]
    exact hsm c _ (foldr_mem hA hf _)
  | add p q hp hq =>
    rw [map_add (f := _)]
    exact hadd _ _ hp hq

private theorem opPow_single_add (hA : ∀ i f, P f → P (A i f))
    (hc : ∀ i j f, P f → A i (A j f) = A j (A i f)) {f : X → ℂ} (hf : P f) (k : ι →₀ ℕ) (v : ι) :
    opPow A (Finsupp.single v 1 + k) f = A v (opPow A k f) := by
  show List.foldr (fun i g => A i g) f (Finsupp.toMultiset (Finsupp.single v 1 + k)).toList =
    List.foldr (fun i g => A i g) f (v :: (Finsupp.toMultiset k).toList)
  apply foldr_perm hA hc hf
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.cons_coe, Multiset.coe_toList, map_add (f := _),
    Finsupp.toMultiset_single, one_nsmul, Multiset.singleton_add]

theorem pure_X_mul (hadd : ∀ f f', P f → P f' → P (f + f')) (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (hA : ∀ i f, P f → P (A i f)) (hc : ∀ i j f, P f → A i (A j f) = A j (A i f))
    (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f')
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f)
    {f : X → ℂ} (hf : P f) (Q : MvPolynomial ι ℂ) (v : ι) :
    pureTensorL A f (MvPolynomial.X v * Q) = A v (pureTensorL A f Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    have hk : P (opPow A k f) := foldr_mem hA hf _
    show pureTensorL A f (MvPolynomial.monomial (Finsupp.single v 1) 1 * MvPolynomial.monomial k c) = _
    rw [MvPolynomial.monomial_mul, one_mul, pure_monomial, pure_monomial,
      opPow_single_add hA hc hf, Asm v c _ hk]
  | add p q hp hq =>
    rw [mul_add, map_add (f := _), map_add (f := _), hp, hq,
      Aadd v _ _ (pure_mem hadd hsm hA hf p) (pure_mem hadd hsm hA hf q)]





end Generic

variable {D : D7} {S T : HSp D} (C : Ctx S T)





variable (τ : D.what₂.Tau) (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
  (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)














end GlobalTheory.Ker.FockAlg
