module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFinPartInCompactBoundedDenominatorStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaConv

theorem exists_den_of_inBox : ∀ (D : D7) (m n : ℕ) (K : Set (Mx D m n)), IsCompact K → ∃ L : ℕ, 0 < L ∧ ∀ (x : Mx D m n) (ξ : Matrix (Fin m) (Fin n) D.host.E), x.map (finPart D) = (ξ.map (incA D) : Mx D m n).map (finPart D) → GlobalTheory.Unf.InBox K x → ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j) := by
  intro D m n K hK
  have hK1 : IsCompact (⋃ p : Fin m × Fin n, (fun x : Mx D m n => x p.1 p.2) '' K) :=
    isCompact_iUnion fun p => hK.image (continuous_id.matrix_elem p.1 p.2)
  obtain ⟨L, hL, h⟩ := GlobalTheory.T.rational_finPart_in_compact_bounded_denominator D _ hK1
  refine ⟨L, hL, fun x ξ hx ⟨k, hk, hxk⟩ i j => ?_⟩
  refine h (k i j) (Set.mem_iUnion.2 ⟨(i, j), k, hk, rfl⟩) (ξ i j) ?_
  have h1 : finPart D (x i j) = finPart D (incA D (ξ i j)) := congrFun (congrFun hx i) j
  have h2 : finPart D (x i j - k i j) = 0 := congrFun (congrFun hxk i) j
  have h3 : finPart D (x i j) - finPart D (k i j) = 0 :=
    ((finPart D).map_sub (x i j) (k i j)).symm.trans h2
  exact h1.symm.trans (sub_eq_zero.1 h3)

end GlobalTheory.ThetaConv
