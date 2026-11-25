module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.RatWeilOp

theorem ind_fourier_self : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure],
    μ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 → (fun y : κ → Fv F v => ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ) = ind κ v := by
  intro F _ _ v ψ hψ κ _ _ _ μ _ hμ
  classical
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hSo : IsOpen {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
    have e : {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} =
        ⋂ i, (fun x : κ → Fv F v => x i) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext; simp
    rw [e]; exact isOpen_iInter_of_finite fun i => hO.preimage (continuous_apply i)
  have hSm := hSo.measurableSet
  have hψO : ∀ z ∈ v.adicCompletionIntegers F, ψ z = 1 := fun z hz => by
    simpa using (hψ 1).2 (v.adicCompletionIntegers F).one_mem z hz
  have hdot : ∀ x y : κ → Fv F v, (∀ i, x i ∈ v.adicCompletionIntegers F) → (∀ i, y i ∈ v.adicCompletionIntegers F) →
      x ⬝ᵥ y ∈ v.adicCompletionIntegers F := fun x y hx hy =>
    (v.adicCompletionIntegers F).sum_mem fun i _ => mul_mem (hx i) (hy i)
  funext y
  by_cases hy : ∀ i, y i ∈ v.adicCompletionIntegers F
  · have e : (fun x => ind κ v x * ψ (x ⬝ᵥ y)) =
        Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
      · have hx' : x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_mem hx', Pi.one_apply, one_mul, hψO _ (hdot x y hx hy)]
      · have hx' : x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_notMem hx', zero_mul]
    have hy' : y ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hy
    rw [e, integral_indicator hSm, setIntegral_const, Measure.real, hμ]
    simp [ind, Set.indicator_of_mem hy']
  · have hy' : y ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hy
    have h0 : ind κ v y = 0 := by simp only [ind, Set.indicator_of_notMem hy']
    rw [h0]
    push_neg at hy
    obtain ⟨i, hi⟩ := hy
    have : ¬ ∀ t ∈ v.adicCompletionIntegers F, ψ (y i * t) = 1 := fun h => hi ((hψ (y i)).1 h)
    push_neg at this
    obtain ⟨t, ht, hne⟩ := this
    have hs : ∀ j, (Pi.single i t : κ → Fv F v) j ∈ v.adicCompletionIntegers F := fun j => by
      by_cases hj : j = i
      · subst hj; simpa using ht
      · simp [Pi.single_apply, hj]
    have hind : ∀ x, ind κ v (Pi.single i t + x) = ind κ v x := fun x => by
      have : (∀ j, ((Pi.single i t : κ → Fv F v) + x) j ∈ v.adicCompletionIntegers F) ↔ ∀ j, x j ∈ v.adicCompletionIntegers F := by
        constructor
        · intro h j
          have := sub_mem (h j) (hs j)
          simpa using this
        · intro h j
          exact add_mem (hs j) (h j)
      by_cases hx : ∀ j, x j ∈ v.adicCompletionIntegers F
      · have h1 : Pi.single i t + x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := this.2 hx
        have h2 : x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_mem h1, Set.indicator_of_mem h2, Pi.one_apply]
      · have h1 : Pi.single i t + x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := fun h => hx (this.1 h)
        have h2 : x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    have key : ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ = ψ (y i * t) * ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ := by
      rw [← integral_const_mul]
      conv_lhs => rw [← integral_add_left_eq_self (μ := μ) (fun x => ind κ v x * ψ (x ⬝ᵥ y)) (Pi.single i t)]
      congr 1
      funext x
      rw [hind, add_dotProduct, single_dotProduct, AddChar.map_add_eq_mul, mul_comm t (y i)]
      ring
    have h1 : (1 - ψ (y i * t)) * ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ = 0 := by
      rw [sub_mul, one_mul, ← key, sub_self]
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (Ne.symm hne))

end GlobalTheory.RatWeilOp
