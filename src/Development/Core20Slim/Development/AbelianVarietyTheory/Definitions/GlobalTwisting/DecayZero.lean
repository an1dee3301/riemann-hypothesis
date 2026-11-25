module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.SWQ

open scoped TensorProduct NNReal ENNReal
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

def qd (R : Type) [CommRing R] [Algebra F R] (a : Fin N → F) (u : Fin N → R) : R :=
  ∑ l, algebraMap F R (a l) * u l ^ 2

def Bd (R : Type) [CommRing R] [Algebra F R] (a : Fin N → F) (u u' : Fin N → R) : R :=
  ∑ l, algebraMap F R (2 * a l) * u l * u' l

def rat (ξ : Fin N → F) : Fin N → AF F := fun l => algebraMap F (AF F) (ξ l)

def inf (u : Fin N → AF F) : Fin N → Ainf F := fun l => fstA F (u l)

def fin (u : Fin N → AF F) : Fin N → Af F := fun l => sndA F (u l)

def re (x : Ainf F) (w : InfinitePlace F) : ℝ :=
  (InfinitePlace.Completion.extensionEmbedding w (x w)).re

def sz (u : Fin N → AF F) : ℝ := ∑ l, ∑ w : InfinitePlace F, |re (inf u l) w|


def Decay (Φ : (Fin N → AF F) → ℂ) : Prop :=
  Continuous Φ ∧ (∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ u, fin u ∉ K → Φ u = 0) ∧
    ∀ k : ℕ, ∃ C : ℝ, ∀ u, ‖Φ u‖ * (1 + sz u) ^ k ≤ C

def IsCov1 (ν : Measure (AF F)) : Prop :=
  ν.IsAddHaarMeasure ∧ ∃ D : Set (AF F), MeasurableSet D ∧
    IsAddFundamentalDomain (algebraMap F (AF F)).range.toAddSubgroup D ν ∧ ν D = 1

def muV (N : ℕ) (ν : Measure (AF F)) : Measure (Fin N → AF F) := Measure.pi fun _ => ν

def IsLam (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) : Prop :=
  (∀ w, lam w ≠ 0) ∧ ∀ x : Ainf F,
    psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, lam w * re x w : ℝ) : ℂ))

def Ctx (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F) : Prop :=
  IsTotallyReal F ∧ IsCharAF F ψ ∧ IsLam ψ lam ∧ IsCov1 ν ∧ ∀ l, a l ≠ 0

variable (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F)

def Ub (b : AF F) (Φ : (Fin N → AF F) → ℂ) : (Fin N → AF F) → ℂ := fun u => ψ (b * qd (AF F) a u) * Φ u

def Da (t : AF F) (Φ : (Fin N → AF F) → ℂ) : (Fin N → AF F) → ℂ := fun u => Φ (t • u)

def Fo (Φ : (Fin N → AF F) → ℂ) : (Fin N → AF F) → ℂ :=
  fun u => ∫ s, Φ s * ψ (Bd (AF F) a s u) ∂(muV N ν)

def rho (x y : Fin N → AF F) (Φ : (Fin N → AF F) → ℂ) : (Fin N → AF F) → ℂ :=
  fun u => ψ (Bd (AF F) a u y + algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y) * Φ (u + x)

def th (Φ : (Fin N → AF F) → ℂ) : ℂ := ∑' ξ : Fin N → F, Φ (rat ξ)

variable {ψ a}

section Herm

variable {E : Type} [Field E] [Algebra F E] {M : ℕ}

end Herm

theorem decay_zero : Decay (fun _ : Fin N → AF F => (0 : ℂ)) :=
  ⟨continuous_const, ⟨∅, isCompact_empty, fun _ _ => rfl⟩, fun _ => ⟨0, fun _ => by simp⟩⟩

end GlobalTheory.SWQ
