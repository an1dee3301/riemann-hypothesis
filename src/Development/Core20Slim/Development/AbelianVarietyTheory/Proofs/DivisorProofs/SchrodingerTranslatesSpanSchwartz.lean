module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabiliserFixesVacuumStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerIrreducibleFinitePlaceCompletion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Invertible
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Map
public import Mathlib.Order.Lattice
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SchrSpan

theorem schr_comp_loc {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  simp only [dotProduct_add, add_dotProduct]
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2

theorem mem_span_schr_of_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) [Invertible (2 : Fv F v)] (χ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ], (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, χ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) →
    ∀ (f₀ : (κ → Fv F v) → ℂ), f₀ ∈ SB (κ → Fv F v) → f₀ ≠ 0 → ∀ (φ : (κ → Fv F v) → ℂ), φ ∈ SB (κ → Fv F v) →
      φ ∈ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr χ w f₀) := by
  intro F _ _ v _ χ κ _ hcond f₀ hf₀ hne φ hφ
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have htriv : ∀ y ∈ v.adicCompletionIntegers F, χ y = 1 := by
    intro y hy
    have := (hcond 1).2 (one_mem _) y hy
    simpa using this
  have hc : Continuous χ := by
    have : IsLocallyConstant χ := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      rw [← map_add_left_nhds_zero, Filter.eventually_map]
      filter_upwards [hO.mem_nhds (zero_mem _)] with s hs
      rw [AddChar.map_add_eq_mul, htriv s hs, mul_one]
    exact this.continuous
  have h1 : χ ≠ 1 := by
    intro h
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    have hπ0 : π ≠ 0 := by
      intro h0; rw [h0, map_zero] at hπ; exact WithZero.zero_ne_coe hπ
    have hmem : ((π⁻¹ : F) : Fv F v) ∈ v.adicCompletionIntegers F :=
      (hcond _).1 (fun y _ => by rw [h]; rfl)
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, hπ] at hmem
    exact absurd hmem (by decide)
  set N := Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr χ w f₀) with hNdef
  have hN : N ≤ GlobalTheory.WeilM.SB (κ → Fv F v) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    show schr χ w f₀ ∈ GlobalTheory.WeilM.SB (κ → Fv F v)
    convert GlobalTheory.SchrSBFin.schr_mem_SB v χ hc w f₀ hf₀ using 2
    all_goals exact Subsingleton.elim _ _
  have hS : ∀ w, ∀ g ∈ N, schr χ w g ∈ N := by
    intro w g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w', rfl⟩ := hx
      rw [schr_comp_loc]
      exact N.smul_mem _ (Submodule.subset_span ⟨w + w', rfl⟩)
    | zero =>
      have : schr χ w (0 : (κ → Fv F v) → ℂ) = 0 := by funext x; simp [schr]
      rw [this]; exact N.zero_mem
    | add a b _ _ ha hb =>
      have : schr χ w (a + b) = schr χ w a + schr χ w b := by funext x; simp [schr, mul_add]
      rw [this]; exact N.add_mem ha hb
    | smul c a _ ha =>
      have : schr χ w (c • a) = c • schr χ w a := by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul]; ring
      rw [this]; exact N.smul_mem c ha
  have h0 : f₀ ∈ N := by
    have : schr χ (0 : (κ → Fv F v) × (κ → Fv F v)) f₀ = f₀ := by funext x; simp [schr]
    rw [← this]; exact Submodule.subset_span ⟨0, rfl⟩
  have hall := GlobalTheory.SchrIrred.schr_irreducible v χ hc h1 N hN
    (fun w g hg => by convert hS w g hg using 2; exact Subsingleton.elim _ _) f₀ h0 hne
  rw [hall]; exact hφ

end GlobalTheory.SchrSpan
