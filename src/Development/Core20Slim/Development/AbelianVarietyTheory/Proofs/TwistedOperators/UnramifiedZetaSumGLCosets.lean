module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.GradedSeriesContinuationDominatedStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumHeckeEigenvalueGeneratingSeriesGLStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParamTrivialBoundUnitaryGLStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeVectorHeckeEigenvalueStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCardCosetsDiagonalDoubleCosetGLStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementE
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Multiset.ZeroCons
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Tactic.Group
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ZetaGL

theorem cartan_existsUnique (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ)
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E))
    (hT : ∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i) (g : GL (Fin r) (w.adicCompletion E)) :
    ∃! d : {d : Fin r → ℤ // Antitone d},
      g ∈ DoubleCoset.doubleCoset (T d.1) (KGL w (n := r) : Set (GL (Fin r) (w.adicCompletion E))) (KGL w (n := r)) := by
  have hm := mem_Ov_of_isUnifV hϖ
  obtain ⟨a, ha, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp E w r ϖ hm hϖ g
  have hg : g = k₁ * T a * k₂ := Units.ext (by rw [e, Units.val_mul, Units.val_mul, hT]; rfl)
  refine ⟨⟨a, ha⟩, DoubleCoset.mem_doubleCoset.2 ⟨k₁, hk₁, k₂, hk₂, hg⟩, ?_⟩
  rintro ⟨a', ha'⟩ h
  obtain ⟨k₁', hk₁', k₂', hk₂', e'⟩ := DoubleCoset.mem_doubleCoset.1 h
  rw [hg] at e'
  have e2 : T a' = (k₁'⁻¹ * k₁) * T a * (k₂ * k₂'⁻¹) := by
    calc T a' = k₁'⁻¹ * (k₁' * T a' * k₂') * k₂'⁻¹ := by group
      _ = _ := by rw [← e']; group
  have e3 := congrArg Units.val e2
  rw [Units.val_mul, Units.val_mul, hT, hT] at e3
  exact Subtype.ext (Formalism.UG.Final.CartanUnique E w r ϖ hm hϖ a a' ha ha' _ (mul_mem (inv_mem hk₁') hk₁) _
    (mul_mem hk₂ (inv_mem hk₂')) e3.symm).symm

theorem differentiable_eulerPoly (B : Multiset ℂˣ) (a : ℂ) : Differentiable ℂ fun X : ℂ => eulerPoly B (a * X) := by
  induction B using Multiset.induction_on with
  | empty => simp [eulerPoly]
  | cons b B ih =>
    simp only [eulerPoly_cons]
    exact (by fun_prop : Differentiable ℂ fun X : ℂ => 1 - (b : ℂ) * (a * X)).mul ih

theorem differentiableOn_eulerFac (B : Multiset ℂˣ) (a : ℂ) (R : ℝ)
    (h : ∀ b ∈ B, ∀ X : ℂ, ‖X‖ < R → ‖(b : ℂ) * (a * X)‖ < 1) :
    DifferentiableOn ℂ (fun X => eulerFac B (a * X)) (Metric.ball 0 R) := fun X hX =>
  ((differentiable_eulerPoly B a X).inv
    (eulerPoly_ne_zero fun b hb => h b hb X (by simpa using hX))).differentiableWithinAt

end GlobalTheory.ZetaGL

namespace GlobalTheory.ZetaGL


end GlobalTheory.ZetaGL
