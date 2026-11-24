module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory

theorem absE_eq_prod_norm_fstA_sndA (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E]
    [NumberField E] [Algebra F E] (y : (AF F ⊗[F] E)ˣ) :
    (∏ w, ‖(fstA F (Algebra.norm (AF F) (y : AF F ⊗[F] E))) w‖) *
      ∏ᶠ v, ‖evalV F v (sndA F (Algebra.norm (AF F) (y : AF F ⊗[F] E)))‖ = (GlobalTheory.Doubling.absE F E y : ℝ) := by
  have hf := GlobalTheory.Doubling.finite_mulSupport_absEv (F := F) (E := E) y
  rw [GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]
  simp only [GlobalTheory.Doubling.absEw_unitInf] at *
  simp only [GlobalTheory.Doubling.absEv_unitFin] at hf ⊢
  rw [show ((∏ᶠ v, ‖GlobalTheory.AdelicU.evFin F v (Algebra.norm (AF F) y.1)‖₊ : ℝ≥0) : ℝ) =
      ∏ᶠ v, ((‖GlobalTheory.AdelicU.evFin F v (Algebra.norm (AF F) y.1)‖₊ : ℝ≥0) : ℝ) from
    NNReal.toRealHom.toMonoidHom.map_finprod hf]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [InfinitePlace.mult, if_pos (IsTotallyReal.isReal w), pow_one, coe_nnnorm]
  rfl

end GlobalTheory
