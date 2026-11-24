module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRepOfActionOnTotalFamily
public import Formalism.LocalRingCardinality.DataTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryRep_of_action_on_total_family : ∀ (G S H : Type) [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (act : G → S → S) (E : S → H), (∀ p, act 1 p = p) → (∀ g h p, act (g * h) p = act g (act h p)) → Dense (Submodule.span ℂ (Set.range E) : Set H) → (∀ g p q, inner ℂ (E (act g p)) (E (act g q)) = inner ℂ (E p) (E q)) → (∀ p q, Continuous fun g => inner ℂ (E q) (E (act g p))) → ∃ π : G →* (H →L[ℂ] H), (∀ g x, ‖π g x‖ = ‖x‖) ∧ (∀ x, Continuous fun g => π g x) ∧ ∀ g p, π g (E p) = E (act g p) := by
  first | exact @GlobalTheory.TotalFamilyRep.exists_rep | exact GlobalTheory.TotalFamilyRep.exists_rep | (intros; apply GlobalTheory.TotalFamilyRep.exists_rep <;> assumption)
