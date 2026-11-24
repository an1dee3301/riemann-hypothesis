module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueAdelicMatrixRealComponentsFinitePartStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPolynomialMulGaussianOfAnnihilatedStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.Slice

variable {D : D7}

theorem compAt_add' (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} (x y : Mx D m n) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y :=
  Matrix.ext fun i j => by
    show θ τ (infPart D (x i j + y i j)) = θ τ (infPart D (x i j)) + θ τ (infPart D (y i j))
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _)]

theorem finMap_add {m n : ℕ} (x y : Mx D m n) :
    (x + y).map (finPart D) = x.map (finPart D) + y.map (finPart D) :=
  Matrix.ext fun i j => by
    show finPart D (x i j + y i j) = finPart D (x i j) + finPart D (y i j)
    rw [RingHom.map_add (f := _)]

theorem slice_polyGauss : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : RealMat V), (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ (N : ℕ), ∀ φ ∈ schwartzA θ V.rank n, (∀ L : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin n) ℂ), L.length = N → L.foldr (fun q g => annS V l s θ q.1 q.2 g) φ = 0) → ∀ x₀ : Mx D V.rank n, ∃ p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ, ∀ x : Mx D V.rank n, x.map (finPart D) = x₀.map (finPart D) → φ x = evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) := by
  intro D θ hθ V n l s hs N φ hφ hL x₀
  have hE := fun z : D.what₂.Tau → Fin V.rank → Fin n → ℂ =>
    GlobalTheory.T.existsUnique_adelicMatrix_realComponents_finitePart D θ hθ V.rank n (fun τ => Matrix.of (z τ)) x₀
  let ι : (D.what₂.Tau → Fin V.rank → Fin n → ℂ) → Mx D V.rank n := fun z => Classical.choose (hE z).exists
  have hι : ∀ z, (∀ τ, compAt θ τ (ι z) = Matrix.of (z τ)) ∧ (ι z).map (finPart D) = x₀.map (finPart D) :=
    fun z => Classical.choose_spec (hE z).exists
  have huniq : ∀ z x, (∀ τ, compAt θ τ x = Matrix.of (z τ)) → x.map (finPart D) = x₀.map (finPart D) → x = ι z :=
    fun z x h1 h2 => (hE z).unique ⟨h1, h2⟩ (hι z)
  have hline : ∀ z τ (X : Matrix (Fin V.rank) (Fin n) ℂ) (w : D.what₂.Tau → Fin V.rank → Fin n → ℂ),
      w τ = X → (∀ τ', τ' ≠ τ → w τ' = 0) → ∀ t : ℝ, ι (z + t • w) = ι z + lineAt θ τ X t := by
    intro z τ X w hw0 hw1 t
    have hLn : IsLineAt θ τ X (lineAt θ τ X) :=
      Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ V.rank n τ X)
    symm
    apply huniq
    · intro τ'
      rw [compAt_add', (hι z).1, hLn.2.2 t τ']
      ext i j
      by_cases h : τ' = τ
      · subst h
        rw [if_pos rfl]
        show z τ' i j + ((t : ℂ) • X) i j = z τ' i j + t • w τ' i j
        rw [hw0, Complex.real_smul]
        rfl
      · rw [if_neg h]
        show z τ' i j + (0 : Matrix (Fin V.rank) (Fin n) ℂ) i j = z τ' i j + t • w τ' i j
        rw [hw1 τ' h]
        simp
    · rw [finMap_add, (hι z).2, hLn.2.1 t, add_zero]
  have hcomm : ∀ τ X (g : Mx D V.rank n → ℂ),
      annC V l s τ X (fun z => g (ι z)) = fun z => annS V l s θ τ X g (ι z) := by
    intro τ X g
    funext z
    simp only [annC, annS]
    congr 1
    · congr 1
      funext t
      congr 1
      apply hline z τ X
      · simp
      · intro τ' h
        simp [h]
    · rw [(hι z).1]
  have hfold : ∀ L : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin n) ℂ),
      L.foldr (fun q g => annC V l s q.1 q.2 g) (fun z => φ (ι z)) =
        fun z => (L.foldr (fun q g => annS V l s θ q.1 q.2 g) φ) (ι z) := by
    intro L
    induction L with
    | nil => rfl
    | cons q L ih => simp only [List.foldr_cons, ih, hcomm]
  have hsm : ∀ ψ : Mx D V.rank n → ℂ, ψ ∈ schwartzA θ V.rank n → ContDiff ℝ ∞ (fun z => ψ (ι z)) := by
    intro ψ hψ
    unfold schwartzA at hψ
    induction hψ using Submodule.span_induction with
    | mem ψ hψ =>
      obtain ⟨f, g, -, rfl⟩ := hψ
      have e : (fun z => f (fun τ i j => compAt θ τ (ι z) i j) * g (fun i j => finPart D (ι z i j))) =
          fun z => f z * g (fun i j => finPart D (x₀ i j)) := by
        funext z
        congr 1
        · congr 1
          funext τ i j
          rw [(hι z).1]
          rfl
        · congr 1
          funext i j
          exact congrFun (congrFun (hι z).2 i) j
      simp only
      rw [e]
      exact (f.smooth ⊤).mul contDiff_const
    | zero => exact contDiff_const
    | add a b _ _ ha hb => exact ha.add hb
    | smul c a _ ha => exact ha.const_smul c
  have hsmooth := hsm φ hφ
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_polynomial_mul_gaussian_of_annihilated D V n l s hs N (fun z => φ (ι z)) hsmooth (fun L hLN => by
    rw [hfold, hL L hLN]
    rfl)
  refine ⟨p, fun x hx => ?_⟩
  have hx' : x = ι (fun τ i j => compAt θ τ x i j) := huniq _ x (fun τ => rfl) hx
  calc φ x = φ (ι (fun τ i j => compAt θ τ x i j)) := by rw [← hx']
    _ = _ := hp _

end GlobalTheory.StdUnn.Slice

end
