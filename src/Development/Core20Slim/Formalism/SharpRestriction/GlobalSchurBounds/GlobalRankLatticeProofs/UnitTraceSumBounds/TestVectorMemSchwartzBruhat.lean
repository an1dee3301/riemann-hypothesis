module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
public import Development.Core20Slim.Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FamilyLogGammaSmallHolds
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Separable
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric NumberField

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])



omit [Fact p.Prime] in
theorem test_vector_mem_schwartz_bruhat (z : D.host.E) : D.host.φ₀ z ∈ Qbar := by
  have h : IsIntegral ℚ z := Algebra.IsIntegral.isIntegral z
  exact mem_algebraicClosure_iff.2 (h.map D.host.φ₀.toRatAlgHom).isAlgebraic

theorem lamPhi_add (x y : D.host.E) : lamC lam (D.host.φ₀ (x + y)) = lamC lam (D.host.φ₀ x) + lamC lam (D.host.φ₀ y) := by
  unfold lamC
  rw [dite_eq_left (test_vector_mem_schwartz_bruhat D (x + y)), dite_eq_left (test_vector_mem_schwartz_bruhat D x), dite_eq_left (test_vector_mem_schwartz_bruhat D y), ← map_add lam]
  exact congrArg lam (Subtype.ext (by simp))

theorem lamPhi_mul (x y : D.host.E) : lamC lam (D.host.φ₀ (x * y)) = lamC lam (D.host.φ₀ x) * lamC lam (D.host.φ₀ y) := by
  unfold lamC
  rw [dite_eq_left (test_vector_mem_schwartz_bruhat D (x * y)), dite_eq_left (test_vector_mem_schwartz_bruhat D x), dite_eq_left (test_vector_mem_schwartz_bruhat D y), ← map_mul lam]
  exact congrArg lam (Subtype.ext (by simp))

theorem okp_add (α β : ℂ_[p] × ℂ_[p]) (hα : α ∈ OKp D lam) (hβ : β ∈ OKp D lam) : α + β ∈ OKp D lam := by
  unfold OKp at hα hβ ⊢
  refine map_mem_closure₂ (f := fun u v : ℂ_[p] × ℂ_[p] => u + v) continuous_add hα hβ ?_
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  refine ⟨a + b, ?_⟩
  have hab : (((a + b : 𝓞 D.host.K) : D.host.K) : D.host.E)
      = ((a : D.host.K) : D.host.E) + ((b : D.host.K) : D.host.E) := by simp
  simp only [tauK, tauKc, hab, map_add D.host.conj, lamPhi_add, Prod.mk_add_mk]


end Formalism.MainNotions.Ext
