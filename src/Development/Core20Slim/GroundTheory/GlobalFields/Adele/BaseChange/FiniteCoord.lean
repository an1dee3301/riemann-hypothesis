module

public import Mathlib
public import Development.Core20Slim.GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap
public import Development.Core20Slim.GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import Development.Core20Slim.GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.Finite
public import Development.Core20Slim.GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct

noncomputable section

namespace AdeleBaseChange

open SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem trace_mem_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] {y : w.adicCompletion L}
    (hy : y ∈ w.adicCompletionIntegers L) :
    Algebra.trace (v.adicCompletion K) (w.adicCompletion L) y ∈ v.adicCompletionIntegers K := by
  open ValuativeRel in
  have hint : IsIntegral 𝒪[v.adicCompletion K] y :=
    isIntegral_of_mem_integer v w ((mem_valuationInteger_iff w y).2 hy)
  have htr : IsIntegral 𝒪[v.adicCompletion K]
      (Algebra.trace (v.adicCompletion K) (w.adicCompletion L) y) :=
    Algebra.isIntegral_trace hint
  exact (mem_valuationInteger_iff v _).1 ((Valuation.integer.integers
    (ValuativeRel.valuation (v.adicCompletion K))).mem_of_integral htr)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

abbrev traceDual : Basis ι K L :=
  (Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) b

theorem trace_mul_traceDual (i j : ι) :
    Algebra.trace K L (b j * traceDual b i) = if j = i then 1 else 0 := by
  rw [mul_comm, ← Algebra.traceForm_apply]
  exact LinearMap.BilinForm.apply_dualBasis_left _ _ i j

def localCoord (v : HeightOneSpectrum (𝓞 K)) (i : ι) :
    CompletionsOver L v →ₗ[v.adicCompletion K] v.adicCompletion K :=
  ((Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i).comp
    (tensorEquiv L v).symm.toLinearEquiv.toLinearMap


omit [DecidableEq ι] in
theorem sum_localCoord (v : HeightOneSpectrum (𝓞 K)) (z : CompletionsOver L v) :
    ∑ i, algebraMap (v.adicCompletion K) (CompletionsOver L v) (localCoord b v i z) *
      algebraMap L (CompletionsOver L v) (b i) = z := by
  have h := (Algebra.TensorProduct.basis (v.adicCompletion K) b).sum_repr
    ((tensorEquiv L v).symm z)
  have h2 := congrArg (tensorEquiv L v) h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [AlgEquiv.apply_symm_apply, map_sum] at h2
  conv_rhs => rw [← h2]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Algebra.TensorProduct.basis_apply, map_smul, tensorEquiv_one_tmul, Algebra.smul_def]
  rfl


omit [Fintype ι] [DecidableEq ι] in
theorem localCoord_algebraMap (v : HeightOneSpectrum (𝓞 K)) (i : ι) (l : L) :
    localCoord b v i (algebraMap L (CompletionsOver L v) l) =
      algebraMap K (v.adicCompletion K) (b.repr l i) := by
  have : (tensorEquiv L v).symm (algebraMap L (CompletionsOver L v) l) = 1 ⊗ₜ l := by
    rw [AlgEquiv.symm_apply_eq, tensorEquiv_one_tmul]
  change (Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i
    ((tensorEquiv L v).symm (algebraMap L (CompletionsOver L v) l)) = _
  rw [this, Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul, one_smul,
    Finsupp.mapRange_apply]

theorem localCoord_eq_sum_trace (v : HeightOneSpectrum (𝓞 K)) (i : ι) (z : CompletionsOver L v) :
    localCoord b v i z = ∑ w : PlacesOver L v, Algebra.trace (v.adicCompletion K)
      (w.1.adicCompletion L) (z w * algebraMap L (w.1.adicCompletion L) (traceDual b i)) := by
  have key : (Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i =
      (Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)).comp
        (LinearMap.mulRight (v.adicCompletion K) (1 ⊗ₜ traceDual b i)) := by
    refine (Algebra.TensorProduct.basis (v.adicCompletion K) b).ext fun j ↦ ?_
    rw [Basis.coord_apply, Basis.repr_self, LinearMap.comp_apply, LinearMap.mulRight_apply,
      Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      trace_one_tmul, trace_mul_traceDual, Finsupp.single_apply]
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  change (Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i
    ((tensorEquiv L v).symm z) = _
  rw [key, LinearMap.comp_apply, LinearMap.mulRight_apply,
    ← Algebra.trace_eq_of_algEquiv (tensorEquiv L v), map_mul, AlgEquiv.apply_symm_apply,
    tensorEquiv_one_tmul, trace_pi]
  rfl

theorem localCoord_mem (v : HeightOneSpectrum (𝓞 K)) (i : ι) (z : CompletionsOver L v)
    (hz : ∀ w : PlacesOver L v,
      z w * algebraMap L (w.1.adicCompletion L) (traceDual b i) ∈ w.1.adicCompletionIntegers L) :
    localCoord b v i z ∈ v.adicCompletionIntegers K := by
  rw [localCoord_eq_sum_trace]
  exact sum_mem fun w _ ↦ trace_mem_adicCompletionIntegers v w.1 (hz w)


omit [Fintype ι] [DecidableEq ι] in
theorem continuous_localCoord (v : HeightOneSpectrum (𝓞 K)) (i : ι) :
    Continuous (localCoord b v i) :=
  IsModuleTopology.continuous_of_linearMap (localCoord b v i)

end AdeleBaseChange

end

end GroundTheory.Global
