module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.HeightProofs.NotMemOfMulExp
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Subtype
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

theorem GlobalTheory.TypeSum.CoefClos.coefSum_cSm_wordF : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (d : ℕ) (L : Fin d → (H →ₗ[ℂ] ℂ)), (∀ a, Sobolev₂ (lieSet ε) σ (L a)) →
    ∀ x : Fin d → H, (∀ a, Sm ε σ (x a)) →
    CSm ε (fun y => ∑ a, L a (σ y (x a))) ∧ ∀ (u : List (Ltr ε)), ∀ y ∈ UJset ε,
      wordF u (fun y => ∑ a, L a (σ y (x a))) y = ∑ a, L a (σ y (wordV σ u (x a))) := by
  intro n ε H _ _ _ σ h d L hL x hx
  have hd : ∀ (v : Fin d → H), (∀ a, Sm ε σ (v a)) → ∀ X ∈ lieSet ε, ∀ y ∈ UJset ε,
      HasDerivAt (fun t : ℝ => ∑ a, L a (σ (y * NormedSpace.exp (t • X)) (v a)))
        (∑ a, L a (σ y (dRep σ X (v a)))) 0 := by
    intro v hv X hX y hy
    refine HasDerivAt.fun_sum fun a _ => ?_
    simpa using CoefLow.hasDerivAt_coef h (hL a) (hv a) hX hy 0
  have hw : ∀ (u : List (Ltr ε)) (a : Fin d), Sm ε σ (wordV σ u (x a)) := by
    intro u a
    induction u with
    | nil => exact hx a
    | cons z u ih =>
      rcases z with X | k
      · exact Sm.word h.1 ih (l := [X.1]) (by simpa using X.2)
      · exact Sm.translate h.1 ih (K_le_UJ k.2)
  refine ⟨⟨fun l y => ∑ a, L a (σ y (Dw σ l (x a))), fun _ _ => rfl, fun l hl X hX g hg => ?_, fun l hl => ?_⟩,
    fun u => ?_⟩
  · exact hd _ (fun a => Sm.word h.1 (hx a) hl) X hX g hg
  · exact continuousOn_finsetSum _ fun a _ => h.continuousOn_coef (hL a) (Sm.word h.1 (hx a) hl)
  · induction u with
    | nil => exact fun _ _ => rfl
    | cons z u ih =>
      intro y hy
      rcases z with X | k
      · have e : (fun t : ℝ => wordF u (fun y => ∑ a, L a (σ y (x a))) (y * NormedSpace.exp (t • X.1))) =
            fun t : ℝ => ∑ a, L a (σ (y * NormedSpace.exp (t • X.1)) (wordV σ u (x a))) :=
          funext fun t => ih _ (mul_mem_UJ hy (exp_mem_UJ X.2 t))
        exact (congrArg (fun f => deriv f 0) e).trans (hd _ (hw u) X.1 X.2 y hy).deriv
      · refine (ih _ (mul_mem_UJ hy (K_le_UJ k.2))).trans (Finset.sum_congr rfl fun a _ => ?_)
        rw [sigma_mul h.1 hy (K_le_UJ k.2)]
        rfl
