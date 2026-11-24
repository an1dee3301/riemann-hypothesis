module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Function
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.List.OfFn
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Fin.Tuple
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.Order.WithBot
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SmVecDeriv

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem contDiff_snoc {k : ℕ} :
    ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (k + 1) → ℝ) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using contDiff_snd
  · simp only [Fin.snoc_castSucc]
    fun_prop

theorem snoc_mem {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ} (hXs : ∀ i, Xs i ∈ lieG G)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (i : Fin (k + 1)) :
    (Fin.snoc Xs X : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) i ∈ lieG G := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hX
  · simpa using hXs j

theorem rep_snoc (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hXs : ∀ i, Xs i ∈ lieG G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (t : Fin k → ℝ) (s : ℝ) (u : H) :
    π (List.ofFn fun i => NormedSpace.exp ((Fin.snoc t s : Fin (k + 1) → ℝ) i •
        (Fin.snoc Xs X : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ) i)).prod u =
      π (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod (π (NormedSpace.exp (s • X)) u) := by
  rw [← rep_mul hπ (expProd_mem_UH hG hXs t) (exp_mem_UH hG hX s)]
  simp [List.ofFn_succ', -List.ofFn_succ]

theorem contDiff_word (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {w : H} (hw : w ∈ smSub G π)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) {l : List (Matrix (Fin n) (Fin n) ℂ)}
    (hl : ∀ Y ∈ l, Y ∈ lieG G) (k : ℕ) (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (hXs : ∀ i, Xs i ∈ lieG G) :
    ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => π (List.ofFn fun i => NormedSpace.exp (p.1 i • Xs i)).prod
      (word π l (π (NormedSpace.exp (p.2 • X)) w)) := by
  induction l generalizing k with
  | nil =>
    have h1 := (hw (k + 1) (Fin.snoc Xs X) (snoc_mem hXs hX)).comp contDiff_snoc
    convert h1 using 2 with p
    exact (rep_snoc hG hπ hXs hX p.1 p.2 w).symm
  | cons Y l ih =>
    have hl' : ∀ Z ∈ l, Z ∈ lieG G := fun Z hZ => hl Z (by simp [hZ])
    have hY := hl Y (by simp)
    have h1 := ih hl' (k + 1) (Fin.snoc Xs Y) (snoc_mem hXs hY)
    have hs : ContDiff ℝ ∞ fun q : ((Fin k → ℝ) × ℝ) × ℝ =>
        (((Fin.snoc q.1.1 q.2 : Fin (k + 1) → ℝ), q.1.2) : (Fin (k + 1) → ℝ) × ℝ) :=
      (contDiff_snoc.comp (contDiff_fst.fst.prodMk contDiff_snd)).prodMk contDiff_fst.snd
    have h2 : ContDiff ℝ ∞ (Function.uncurry fun (p : (Fin k → ℝ) × ℝ) (r : ℝ) =>
        π (List.ofFn fun i => NormedSpace.exp (p.1 i • Xs i)).prod (π (NormedSpace.exp (r • Y))
          (word π l (π (NormedSpace.exp (p.2 • X)) w)))) := by
      convert h1.comp hs using 1
      funext q
      exact (rep_snoc hG hπ hXs hY q.1.1 q.2 _).symm
    have h3 := (ContDiff.fderiv (𝕜 := ℝ) (m := ∞) (n := ∞) (g := fun _ : (Fin k → ℝ) × ℝ => (0 : ℝ)) h2
      contDiff_const (le_of_eq rfl)).clm_apply (contDiff_const (c := (1 : ℝ)))
    convert h3 using 2 with p
    have hu := word_mem hG hπ hl' (rep_mem hG hπ hw (exp_mem_UH hG hX p.2))
    have h4 := (((π _).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dRep hu hY) :
      HasDerivAt (fun r : ℝ => π (List.ofFn fun i => NormedSpace.exp (p.1 i • Xs i)).prod
        (π (NormedSpace.exp (r • Y)) (word π l (π (NormedSpace.exp (p.2 • X)) w)))) _ 0)
    exact h4.deriv.symm

theorem contDiff_word_curve (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {w : H} (hw : w ∈ smSub G π)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) {l : List (Matrix (Fin n) (Fin n) ℂ)}
    (hl : ∀ Y ∈ l, Y ∈ lieG G) :
    ContDiff ℝ ∞ fun s : ℝ => word π l (π (NormedSpace.exp (s • X)) w) := by
  have h1 := (contDiff_word hG hπ hw hX hl 0 Fin.elim0 (fun i => i.elim0)).comp
    ((contDiff_const (c := (0 : Fin 0 → ℝ))).prodMk (contDiff_id (E := ℝ)))
  simpa [Function.comp_def, rep_one hπ] using h1

theorem hasDerivAt_word : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) → ∀ w ∈ smSub G (trRep σ P), ∀ X ∈ lieG G, HasDerivAt (fun t : ℝ => word (trRep σ P) l ((trRep σ P) (NormedSpace.exp (t • X)) w)) (word (trRep σ P) l (dRep (trRep σ P) X w)) 0 := by
  intro n ε H _ _ _ σ P G hP h hσ l hl w hw X hX
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  have h1 := ((contDiff_word_curve hG hπ hw hX hl).differentiable (by simp) 0).hasDerivAt
  convert h1 using 1
  refine ext_inner_smooth hP h hσ fun u hu => ?_
  obtain ⟨u', -, h2⟩ := word_adjoint hG hπ hl hu
  have h3 := (hasDerivAt_const (0 : ℝ) u).inner ℂ h1
  have h4 := (hasDerivAt_const (0 : ℝ) u').inner ℂ (hasDerivAt_dRep hw hX)
  simp only [h2 _ (rep_mem hG hπ hw (exp_mem_UH hG hX _)), inner_zero_left, add_zero] at h3 h4
  rw [h2 _ (dRep_mem hG hπ hw hX)]
  exact h4.unique h3

end GlobalTheory.SmVecDeriv

end
