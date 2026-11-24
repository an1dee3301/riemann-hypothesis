module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorsModerateGrowthSmoothFrechetRep
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.List.Basic
public import Init.Prelude
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vectors_moderate_growth_smooth_frechet_rep : ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (ρ : Mx n → (E →L[ℂ] E)), ModRep ε ρ → IsClosed (Fam ε ρ : Set (List (lie (Jm ε)) → E)) ∧ ∃ (p : ℕ → Seminorm ℂ (Fam ε ρ)) (π dπ : Mx n → (Fam ε ρ →L[ℂ] Fam ε ρ)), IsSmoothModRep ε p π dπ ∧ (∀ (g : Mx n) (hg : g ∈ UJset ε) (v : Fam ε ρ) (l : List (lie (Jm ε))), (π g v).1 l = ρ g (v.1 (l.map (adInv hg)))) ∧ (∀ (X : lie (Jm ε)) (v : Fam ε ρ) (l : List (lie (Jm ε))), (dπ (X : Mx n) v).1 l = v.1 (l ++ [X])) ∧ ∀ v : Fam ε ρ, ‖v.1 []‖ ≤ p 0 v := by
  first | exact @GlobalTheory.TypeSum.SmoothFrechet.smooth_frechet_rep | exact GlobalTheory.TypeSum.SmoothFrechet.smooth_frechet_rep | (intros; apply GlobalTheory.TypeSum.SmoothFrechet.smooth_frechet_rep <;> assumption)
