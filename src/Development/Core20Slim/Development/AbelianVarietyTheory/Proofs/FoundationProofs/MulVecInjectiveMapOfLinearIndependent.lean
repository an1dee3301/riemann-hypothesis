module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.ProdFormula
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Formalism.HermitianLattices.StatementMaj
public import Formalism.QuotientMetricDivisors.Statement
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem mulVec_injective_map_of_linearIndependent {K L : Type} [Field K] [Field L] (σ : K →+* L) {d j : ℕ}
    (e : Fin j → Fin d → K) (he : LinearIndependent K e) :
    Function.Injective (((Matrix.of e)ᵀ).map σ).mulVec := by
  letI : Algebra K L := σ.toAlgebra
  rw [Matrix.mulVec_injective_iff]
  have h := (linearIndependent_algebraMap_comp_iff (S := L) (v := e)).2 he
  exact h

theorem gram_eq_conjTranspose_mul {K : Type} [Field K] [NumberField K] [StarRing K] {d j : ℕ}
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) (e : Fin j → Fin d → K) :
    gram X v e = ((X v)⁻¹ * ((Matrix.of e)ᵀ).map v.embedding)ᴴ * ((X v)⁻¹ * ((Matrix.of e)ᵀ).map v.embedding) := by
  ext a b
  simp only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.of_apply]
  rw [Matrix.mul_apply]
  rfl

theorem gramR_ne_zero_and_gram_posDef : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (d j : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), IsMetric H X → ∀ e : Fin j → Fin d → K, LinearIndependent K e → gramR H e ≠ 0 ∧ ∀ v, (gram X v e).PosDef := by
  intro K _ _ _ _ v0 hv0 d j H X hX e he
  have hpos : ∀ v, (gram X v e).PosDef := by
    intro v
    rw [gram_eq_conjTranspose_mul]
    refine Matrix.PosDef.conjTranspose_mul_self _ ?_
    have h1 : Function.Injective ((X v)⁻¹).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.2
        ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ (hX v).1))
    have h2 := mulVec_injective_map_of_linearIndependent v.embedding e he
    intro x y hxy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hxy
    exact h2 (h1 hxy)
  refine ⟨?_, hpos⟩
  have key : v0.embedding (gramR H e) = (gram X v0 e).det := by
    unfold gramR
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    set σ := v0.embedding
    have hM : H.map σ = ((X v0)⁻¹).conjTranspose * (X v0)⁻¹ := (hX v0).2.symm
    ext a b
    rw [Matrix.map_apply, Matrix.of_apply, RingHom.map_dotProduct]
    have hmv : (⇑σ ∘ (H *ᵥ e b)) = H.map σ *ᵥ (⇑σ ∘ e b) :=
      funext fun i => RingHom.map_mulVec σ _ _ i
    have hs : (⇑σ ∘ star (e a)) = star (⇑σ ∘ e a) := by
      funext i
      simp only [Function.comp_apply, Pi.star_apply]
      rw [← starRingEnd_apply]
      exact hv0 (e a i)
    rw [hmv, hs, hM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    simp only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.of_apply]
    rfl
  intro h0
  rw [h0, map_zero] at key
  exact (hpos v0).det_pos.ne key

end GlobalTheory.TestLat
