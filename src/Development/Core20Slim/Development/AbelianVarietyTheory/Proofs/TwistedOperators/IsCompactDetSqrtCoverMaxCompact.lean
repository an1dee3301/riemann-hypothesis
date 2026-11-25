module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Upqcpt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.BlockOrderedSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
public import Formalism.LocalRingCardinality.DataTheta
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Order.SetNotation
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

theorem isClosed_Kset {p q : ℕ} (T : GrpData p q) : IsClosed T.Kset := by
  have h : T.Kset = ⋂ a, ⋂ b, ⋂ (_ : ¬ sameBlock a b), {x : T.G | matG T x a b = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact Iff.rfl
  rw [h]
  refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ => ?_
  exact isClosed_eq ((continuous_matG T).matrix_elem a b) continuous_const

theorem isCompact_Kset : ∀ (p q : ℕ) (T : GrpData p q), IsCompact T.Kset := by
  intro p q T
  have hS : IsCompact ((Units.val : ℂˣ → ℂ) ⁻¹' Metric.sphere 0 1) := by
    refine (Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff ?_).2 (isCompact_sphere 0 1)
    intro z hz
    have : z ≠ 0 := by rintro rfl; simp at hz
    exact ⟨Units.mk0 z this, rfl⟩
  have hc := Formalism.UG.P.isCompact_units_of_unitary (n := Ix p q) (T := {M | star M * M = 1})
    (isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const) (fun M hM => hM)
  refine ((GlobalTheory.RealPar.SqInt.isClosedEmbedding_emb T).isCompact_preimage (hc.prod hS)).of_isClosed_subset
    (isClosed_Kset T) fun x hx => ⟨matG_star_mul T hx, ?_⟩
  simpa using GlobalTheory.RealPar.Cover.norm_sq x

end GlobalTheory.PolarU
