module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.BlockOrderedSquareIntegrable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFdegSmulOfIsDS
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
public import Formalism.FormalDegreeBessel.StatementBF
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters GlobalTheory.RealPar Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.Published.CoverSeries

variable {p q n : ℕ}

def pull {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) : URep T where
  H := H
  π := { toFun := fun x => σ (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q))
         map_one' := by simpa using hσ.1.1
         map_mul' := fun x y => by
           rw [ContinuousLinearMap.mul_def, ← hσ.1.2 _ (h.cov_mem T x) _ (h.cov_mem T y)]
           simp [Matrix.submatrix_mul_equiv] }
  isom x v := hσ.2.1 _ (h.cov_mem T x) v
  cont v := (hσ.2.2 v).comp_continuous
    ((Units.continuous_val.comp (continuous_fst.comp T.emb.continuous)).matrix_reindex e e) (h.cov_mem T)



end GlobalTheory.Published.CoverSeries

end
