module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjExt

open GlobalTheory.ConjDS GlobalTheory.LowTypeDetermined

section Gen

variable {n : ℕ} {ε ε' : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}









end Gen

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}


theorem smooth_translate (M : DSModel V S) (τ : D.what₂.Tau) (u : M.sm τ) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ UJset (M.ε τ)) : SmoothVec (lieAt V τ) (M.rep τ) (M.σ τ g u) := by
  obtain ⟨_, -, hσ, -⟩ := M.ds τ
  have hs : M.sm τ = smooth (gramAt D V τ) (M.rep τ) := Submodule.span_eq (smooth (gramAt D V τ) (M.rep τ))
  have hP := M.fr_unit τ
  have h := M.fr_gram τ
  have hu' : (u : M.H τ) ∈ smooth (gramAt D V τ) (M.rep τ) := hs ▸ u.2
  have e : M.rep τ ((M.fr τ)⁻¹ * g * M.fr τ) = M.σ τ g := congrArg (M.σ τ) (conj_conj hP g)
  rw [← e]
  exact translate_mem (isUnit_gram hP h) (isURepOn_conj hσ hP h) (conj_inv_mem hP h hg) hu'


end GlobalTheory.ConjExt
