module

public import Mathlib
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ProjOp
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set

namespace PositivityTheory.Rg.Sw.AbsSt.Proj

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

def kM {n : ℕ} (a b : Matrix (Fin n) (Fin n) ℂ) : M2 n :=
  fromBlocks ((1 / 2 : ℂ) • (a + b)) ((Complex.I / 2) • (a - b)) (-((Complex.I / 2) • (a - b))) ((1 / 2 : ℂ) • (a + b))

def KIso : Prop := ∀ n : ℕ,
  (∀ a b : Matrix (Fin n) (Fin n) ℂ, a ∈ unitaryGroup (Fin n) ℂ → b ∈ unitaryGroup (Fin n) ℂ →
      ∃ k : GR n, k ∈ KR n ∧ mR k = kM a b) ∧
  (∀ a b a' b' : Matrix (Fin n) (Fin n) ℂ, kM a b * kM a' b' = kM (a * a') (b * b')) ∧ kM (1 : Matrix (Fin n) (Fin n) ℂ) 1 = 1 ∧
  (∀ a b : Matrix (Fin n) (Fin n) ℂ, u1 (kM a b) = a ∧ u2 (kM a b) = b) ∧
  (∀ a : Matrix (Fin n) (Fin n) ℂ, (kM a a).toBlocks₂₁ = 0) ∧
  ∀ k : GR n, k ∈ KR n → u1 (mR k) ∈ unitaryGroup (Fin n) ℂ ∧ u2 (mR k) ∈ unitaryGroup (Fin n) ℂ ∧
    mR k = kM (u1 (mR k)) (u2 (mR k))

def RepKer : Prop := ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H]
  [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure] (V : Submodule ℂ (H → ℂ)), FiniteDimensional ℂ V →
    (∀ φ ∈ V, Continuous φ) → (∀ φ ∈ V, ∀ a : H, (fun x => φ (a * x)) ∈ V) →
    ∃ κ : H → ℂ, Continuous κ ∧ (∀ f : H → ℂ, Continuous f → (fun x => ∫ v, κ v * f (x * v) ∂μ) ∈ V) ∧
      ∀ φ ∈ V, ∀ x, ∫ v, κ v * φ (x * v) ∂μ = φ x

end PositivityTheory.Rg.Sw.AbsSt.Proj
