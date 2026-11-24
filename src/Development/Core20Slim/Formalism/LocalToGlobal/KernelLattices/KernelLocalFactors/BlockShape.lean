module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Formalism.ThetaSupremumBounds.StatementE
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
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
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Sum.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial

noncomputable section

namespace Formalism.L2.Ker.Shape

open Formalism.BasicNotions Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Col

section Alg

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

def dPart (s : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) : DVar ι a b →₀ ℕ :=
  s.comapDomain Sum.inr Sum.inr_injective.injOn

private theorem jetLin_monomial' (J : (DVar ι a b →₀ ℕ) → K)
    (s : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (r : K) :
    jetLin J (MvPolynomial.monomial s r) =
      r • MvPolynomial.monomial (s.comapDomain Sum.inl Sum.inl_injective.injOn) (J (dPart s)) := by
  have h1 : MvPolynomial.monomial s r = r • MvPolynomial.monomial s (1 : K) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [h1, LinearMap.map_smul]
  congr 1
  unfold jetLin
  rw [show (MvPolynomial.monomial s (1 : K)) = MvPolynomial.basisMonomials _ K s by
    simp [MvPolynomial.coe_basisMonomials], Module.Basis.constr_basis]
  all_goals rfl

theorem map_jetLin {L : Type} [Field L] (σ : K →+* L) (J : (DVar ι a b →₀ ℕ) → K)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    MvPolynomial.map σ (jetLin J Q) = jetLin (fun m => σ (J m)) (MvPolynomial.map σ Q) := by
  refine MvPolynomial.induction_on' Q (fun s r => ?_) (fun p q hp hq => ?_)
  · rw [MvPolynomial.map_monomial, jetLin_monomial', jetLin_monomial', MvPolynomial.smul_monomial,
      MvPolynomial.smul_monomial, MvPolynomial.map_monomial, smul_eq_mul, smul_eq_mul, map_mul]
  · rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]

theorem map_frDet {L : Type} [Field L] (σ : K →+* L) (τ : ι) :
    MvPolynomial.map σ (frDet K a τ) = frDet L a τ := by
  unfold frDet
  rw [RingHom.map_det]
  congr 1
  ext α s
  simp [RingHom.mapMatrix_apply, MvPolynomial.map_X]

theorem map_subD {L : Type} [Field L] (σ : K →+* L) (P : Pol K ι a) :
    MvPolynomial.map σ (subD K ι a b P) = subD L ι a b (MvPolynomial.map σ P) := by
  have h : (MvPolynomial.map σ).comp (subD K ι a b).toRingHom =
      (subD L ι a b).toRingHom.comp (MvPolynomial.map σ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [subD]
    · intro v
      show MvPolynomial.map σ (subD K ι a b (MvPolynomial.X v)) = subD L ι a b (MvPolynomial.map σ (MvPolynomial.X v))
      rw [MvPolynomial.map_X]
      simp only [subD, MvPolynomial.aeval_X]
      split_ifs <;> simp
  exact RingHom.congr_fun h P

theorem map_jetMap {L : Type} [Field L] (σ : K →+* L) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    MvPolynomial.map σ (jetMap J n P) =
      jetLin (fun m => σ (J m)) (subD L ι a b (MvPolynomial.map σ P * ∏ τ, frDet L a τ ^ n τ)) := by
  simp only [jetMap, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulRight_apply]
  rw [map_jetLin, map_subD, map_mul, map_prod]
  simp only [map_pow, map_frDet]

end Alg

section Scale

variable {ι : Type} [Fintype ι] {a b : ℕ}

end Scale

section Lift

end Lift

section Base

variable {X : Fields} (A : Amb X) {a b : ℕ} (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
  (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)
  (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB)
  (c : ℕ) (x : HomE X.E a b)

end Base

end Formalism.L2.Ker.Shape
