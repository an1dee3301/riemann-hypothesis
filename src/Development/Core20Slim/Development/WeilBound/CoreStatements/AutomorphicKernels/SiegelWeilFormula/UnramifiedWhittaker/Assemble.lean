module

public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.TraceDual
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Development.Core20Slim.Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

variable {F : Type} [Field F] [NumberField F]

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter
open scoped TensorProduct

theorem unrWhitX_of_parts (hC : LocC) (hA : AlmostGood) : UnrWhitX := by
  intro F E _ _ _ _ _ σ hσ M J hJ n T hT hdet d bs ψ hψ
  refine ⟨(n : ℝ) ^ 2, ?_⟩
  filter_upwards [hA F E σ hσ M J hJ n T hT hdet d bs ψ hψ] with v hv
  obtain ⟨S, σS, ϖ, ε, hε, hG⟩ := hv
  intro μv νv lam L hμ hν hlam hL z hz
  rw [← hε]
  exact hC F E σ M n d J T hT bs v (psiV F ψ v) S σS ϖ ε hG μv νv lam L hμ hν hlam hL z hz

theorem eSp_eq (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ e : ℤˣ, ((e : ℤ) : ℂ) = eSp E v := by
  unfold eSp
  split_ifs
  · exact ⟨-1, by simp⟩
  · exact ⟨1, by simp⟩

theorem unrWhitAll_of_X (h : UnrWhitX) : UnrWhitAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ n T hT hdet d bs ψ hψ
  obtain ⟨t, ht⟩ := h F E σ hσ M J hJ n T hT hdet d bs ψ hψ
  refine ⟨t, ?_⟩
  filter_upwards [ht] with v hv
  obtain ⟨e, he⟩ := eSp_eq E v
  exact ⟨e, fun μv νv lam L hμ hν hlam hL z hz => by rw [he]; exact hv μv νv lam L hμ hν hlam hL z hz⟩

theorem unrWhitAll_of_parts (hC : LocC) (hA : AlmostGood) : UnrWhitAll := unrWhitAll_of_X (unrWhitX_of_parts hC hA)

theorem unrWhit_of_all (h : UnrWhitAll) : UnrWhit :=
  fun F E _ _ _ _ _ σ hσ M J hJ n _ T hT hdet d bs ψ hψ => h F E σ hσ M J hJ n T hT hdet d bs ψ hψ

theorem unrWhit_of_parts (hC : LocC) (hA : AlmostGood) : UnrWhit := unrWhit_of_all (unrWhitAll_of_parts hC hA)

end PositivityTheory.SiegelWeilFormula.Gunr

end
