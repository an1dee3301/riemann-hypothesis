module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianOrthogonal
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PBoundedInverseCompact
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Algebra.NoZeroSMulDivisors.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Defs
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [IsTotallyReal F] in
theorem ShortestVectorIndex.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : LineIndexCoeffs.Statement (E := E) W) (h₂ : LineCoeffsFG.Statement (E := E) W)
    (h₃ : WeightedLenSmul.Statement h v) (h₄ : WeightPos.Statement h v)
    (h₅ : WeightedIndexBound.Statement E) : ShortestVectorIndex.Statement h v := by
  intro M r ha D La g x hD hx hx0 hmin
  set c : InfinitePlace E → ℝ := fun w =>
    (star (invApply g (vecAt v x) w) ⬝ᵥ (M.P w *ᵥ invApply g (vecAt v x) w)).re with hc
  have hcpos : ∀ w, 0 < c w := h₄ M g x hx0
  have hdeg : finrank ℚ E = 2 * finrank ℚ F := by
    rw [← Module.finrank_mul_finrank ℚ F E, Algebra.IsQuadraticExtension.finrank_eq_two F E,
      mul_comm]

  have hlen : ∀ a : E, M.len (invApply g (vecAt v (a • x))) ^ 2 =
      ∑ w, c w * ‖w.embedding a‖ ^ 2 := by
    intro a
    rw [h₃ M g x a]
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  have hlen1 : M.len (invApply g (vecAt v x)) ^ 2 = ∑ w, c w := by
    have := hlen 1
    simpa using this
  have hsub : intSubgroup E ≤ lineCoeffs La x := by
    rintro _ ⟨a, rfl⟩
    exact hD.isLattice.smul_mem a x hx
  have hfg : (lineCoeffs La x).FG := h₂ La x hD.isLattice.fg hx0
  have hmin' : ∀ a ∈ lineCoeffs La x, a ≠ 0 →
      ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2 := by
    intro a haA ha0
    have hax : a • x ∈ La := haA
    have hax0 : a • x ≠ 0 := smul_ne_zero ha0 hx0
    have hle := hmin (a • x) hax hax0
    rw [← hlen1, ← hlen a]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  obtain ⟨a, hali, habs⟩ := ha
  have ha' : ∃ b : Fin (finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (b i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (b i)‖ ≤ r :=
    ⟨a ∘ Fin.cast hdeg, hali.comp _ (Fin.cast_injective hdeg), fun i σ => habs _ σ⟩
  have key := h₅ c hcpos (lineCoeffs La x) hsub hfg hmin' r ha'
  rw [h₁ La x hx0]
  rw [hdeg] at key
  push_cast at key
  exact key

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
