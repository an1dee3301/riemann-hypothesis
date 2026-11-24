module

public import Mathlib
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

open MeasureTheory
open scoped Matrix ComplexConjugate

def hermC (n : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) ℂ) := selfAdjoint _

theorem mem_hermC {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} : b ∈ hermC n ↔ b.IsHermitian := by
  unfold hermC
  rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
  exact Iff.rfl

theorem isClosed_hermC (n : ℕ) : IsClosed (hermC n : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hset : (hermC n : Set (Matrix (Fin n) (Fin n) ℂ)) = {b | star b = b} := rfl
  rw [hset]
  exact isClosed_eq continuous_star continuous_id

instance measHermC (n : ℕ) : MeasurableSpace (hermC n) := borel _

instance borelHermC (n : ℕ) : BorelSpace (hermC n) := ⟨rfl⟩

instance locCompactHermC (n : ℕ) : LocallyCompactSpace (hermC n) :=
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  (isClosed_hermC n).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance secondCountableHermC (n : ℕ) : SecondCountableTopology (hermC n) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _

def detW {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) : ℝ := (Matrix.det (1 + b * b)).re

def gramC {n M : ℕ} (J : Matrix (Fin M) (Fin M) ℂ) (X : Fin n → Fin M → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun a c => ∑ i, ∑ j, conj (X a i) * J i j * X c j

def phaseM {W : Type} [Fintype W] {n M : ℕ} (J : W → Matrix (Fin M) (Fin M) ℂ)
    (B : W → Matrix (Fin n) (Fin n) ℂ) (X : W → Fin n → Fin M → ℂ) : ℝ :=
  ∑ w, (Matrix.trace (B w * gramC (J w) (X w))).re

def coreC {W : Type} [Fintype W] {n M : ℕ} (J : W → Matrix (Fin M) (Fin M) ℂ)
    (μ : Measure (W → Fin n → Fin M → ℂ)) (g : (W → Fin n → Fin M → ℂ) → ℂ) (b : W → hermC n) : ℂ :=
  ∫ X, g X * Complex.exp (2 * Real.pi * Complex.I *
    ((phaseM J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) X : ℝ) : ℂ)) ∂μ

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
