module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ENNReal

namespace GlobalTheory.Unf

variable {D : D7}

def realSize (θ : InfFam D) {m n : ℕ} (x : Mx D m n) : ℝ := ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖

def InBox {m n : ℕ} (K : Set (Mx D m n)) (x : Mx D m n) : Prop := ∃ k ∈ K, (x - k).map (finPart D) = 0


open Classical in
def maj (θ : InfFam D) {m n : ℕ} (K : Set (Mx D m n)) (N : ℕ) (x : Mx D m n) : ℝ :=
  if InBox K x then ((1 + realSize θ x) ^ N)⁻¹ else 0

def supSob (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (d : ℕ) (f : WO S T → ℂ) : ℝ≥0∞ :=
  GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) d f

structure IsSobForm (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (ℓ : (WO S T → ℂ) → ℂ) : Prop where
  add : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f + g) = ℓ f + ℓ g
  smul : ∀ (c : ℂ) f, IsThetaFunO ψ S T f → ℓ (c • f) = c * ℓ f
  bound : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (d : ℕ) (C : NNReal),
    ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ‖ℓ f‖ₑ ≤ C * supSob ψ θ d f

theorem realSize_nonneg (θ : InfFam D) {m n : ℕ} (x : Mx D m n) : 0 ≤ realSize θ x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem maj_nonneg (θ : InfFam D) {m n : ℕ} (K : Set (Mx D m n)) (N : ℕ) (x : Mx D m n) : 0 ≤ maj θ K N x := by
  unfold maj
  split_ifs
  · have := realSize_nonneg θ x; positivity
  · exact le_rfl

end GlobalTheory.Unf

end
