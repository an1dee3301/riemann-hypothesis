module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Formalism.LocalRingCardinality.DataKernels
public import Formalism.LocalToGlobal.HermitianColumns.HermCols
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TotallySplit

@[expose] public section

noncomputable section

namespace GlobalTheory.SplitInterDet

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU  
open Formalism.UG (GLint bc)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}











private theorem algebra_norm_prod_pair_eq_mul {K : Type} [Field K] (a b : K) : Algebra.norm K ((a, b) : K × K) = a * b := by
  rw [Algebra.norm_apply]
  have e : Algebra.lmul K (K × K) (a, b) = LinearMap.prodMap (LinearMap.mulLeft K a) (LinearMap.mulLeft K b) := by
    refine LinearMap.ext fun p => Prod.ext ?_ ?_ <;> simp
  rw [e, LinearMap.det_prodMap, LinearMap.det_mulLeft, LinearMap.det_mulLeft]

theorem norm_eq_split (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (x : Fv F v ⊗[F] E) :
    Algebra.norm (Fv F v) x = splitProj τ x * splitProj (τ.comp σ) x := by
  rw [← Algebra.norm_eq_of_algEquiv (splitAlgEquiv h τ) x, splitAlgEquiv_apply]
  exact algebra_norm_prod_pair_eq_mul _ _




end GlobalTheory.SplitInterDet

end
