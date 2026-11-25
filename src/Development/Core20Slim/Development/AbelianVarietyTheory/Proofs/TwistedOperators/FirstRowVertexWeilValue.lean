module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.EdgeFactorNeZero
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowArgumentConjugateMoveLeftMulInvComponentStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedTensorEigenvalueLaws
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.BinderNameHint
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Nat.Lemmas
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Push
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FirstRowTermLaw

theorem law_gen {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (ht : t ∈ U) {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ}
    (hτ : S.IsExpansion t Φ β τ) (k : FinPt G (.grid 0 D.R.m)) (lam : locPl G t → ℂ)
    (hlam : ∀ w : locPl G t, (locGrid G t w).pathAct .one (GlobalTheory.SplitFlip.oppositePath D.R.m)
      (Pi.mulSingle (0, D.R.m) (kapAt S t w k)) (Tflip W S.B t Φ w) = lam w • Tflip W S.B t Φ w)
    (s : ℂ) (hs : s * ∏ w, lam w = ∏ w : locPl G t, (locGrid G t w).edgeFactor .one (Pi.mulSingle (0, D.R.m) (kapAt S t w k)) (.ex 0 D.R.m))
    (xs : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
    (ys : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    s * (τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i)) =
      τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (ys i) := by
  obtain ⟨e, he, hsupp, hexp⟩ := hτ
  have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
  by_cases hh : (∀ j, IsHalf e (xs j)) ∧ ∀ i, IsHalf e (ys i)
  · have hh' : ∀ i, IsHalf e (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i) := by
      intro i
      by_cases h : i = (GlobalTheory.FirstRowVertex.firstIx D)
      · subst h; rw [Function.update_self]; exact (GlobalTheory.SchrMove.isHalf_actO_iff _ _ _).2 (hh.2 _)
      · rw [Function.update_of_ne h]; exact hh.2 i
    rw [hexp xs _ hh.1 hh', hexp xs ys hh.1 hh.2]
    have hloc : ∀ w : locPl G t, (locGrid G t w).edgeFactor .one (Pi.mulSingle (0, D.R.m) (kapAt S t w k)) (.ex 0 D.R.m) *
        (S.term t Φ β w).datum (S.colAt t w xs) (S.rowAt t w (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))))) =
        lam w * (S.term t Φ β w).datum (S.colAt t w xs) (S.rowAt t w ys) := by
      intro w
      rw [GlobalTheory.T.firstRowArgument_conjugateMove_left_mul_inv_component S ht w w.2 k ys]
      exact GlobalTheory.FirstRowTermLaw.datum_law (Γ := locGrid G t w) one_le_sLen hm _ _ _ _ _ _ _ _ (hlam w) _ _
    have hprod := Finset.prod_congr rfl fun w (_ : w ∈ Finset.univ) => hloc w
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hprod
    exact key_cancel _ _ _ _ _ (Finset.prod_ne_zero_iff.2 fun w _ => edgeFactor_ne_zero _ _ _) hs hprod
  · have hz : ∀ d ∈ τ.support, (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (ys i) = 0 ∧
        (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i) = 0 := by
      intro d hd
      have hX : ∀ j, (d.1 j).fn (xs j) ≠ 0 → IsHalf e (xs j) := fun j h => ((hsupp d hd).1 j).2.1 ▸ (d.1 j).sb.1 _ h
      have hY : ∀ i y, (d.2 i).fn y ≠ 0 → IsHalf e y := fun i y h => ((hsupp d hd).2 i).2.1 ▸ (d.2 i).sb.1 _ h
      by_cases hx : ∀ j, IsHalf e (xs j)
      · obtain ⟨i, hi⟩ : ∃ i, ¬ IsHalf e (ys i) := by
          by_contra hc; push_neg at hc; exact hh ⟨hx, hc⟩
        have h1 : (d.2 i).fn (ys i) = 0 := by by_contra h; exact hi (hY i _ h)
        have h2 : (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i) = 0 := by
          by_contra h
          have h' := hY i _ h
          by_cases hi0 : i = (GlobalTheory.FirstRowVertex.firstIx D)
          · subst hi0; rw [Function.update_self] at h'; exact hi ((GlobalTheory.SchrMove.isHalf_actO_iff _ _ _).1 h')
          · rw [Function.update_of_ne hi0] at h'; exact hi h'
        exact ⟨by rw [show (∏ i, (d.2 i).fn (ys i)) = 0 from Finset.prod_eq_zero (Finset.mem_univ i) h1, mul_zero],
          by rw [show (∏ i, (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i)) = 0 from
            Finset.prod_eq_zero (Finset.mem_univ i) h2, mul_zero]⟩
      · push_neg at hx
        obtain ⟨j, hj⟩ := hx
        have h1 : (d.1 j).fn (xs j) = 0 := by by_contra h; exact hj (hX j h)
        rw [show (∏ j, (d.1 j).fn (xs j)) = 0 from Finset.prod_eq_zero (Finset.mem_univ j) h1]
        simp only [zero_mul, and_self]
    simp only [Finsupp.sum]
    rw [Finset.sum_eq_zero fun d hd => by rw [mul_assoc, (hz d hd).2, mul_zero],
      Finset.sum_eq_zero fun d hd => by rw [mul_assoc, (hz d hd).1, mul_zero], mul_zero]

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw


end GlobalTheory.FirstRowTermLaw

end
