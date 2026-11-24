module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.DivMod.Bootstrap
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.FiniteType

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid

namespace GlobalTheory.FunObj

theorem squareTriple_sig_rank_lt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
    (W : G.Weil) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j) (M : Vol G) (hM : M.Is t),
    ∃ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D (G.V (.grid (i + 1) (j + 1))) τ) ((G.V (.grid (i + 1) (j + 1))).rank - p) p) ∧
      (G.V (.grid i (j + 1))).rank + (G.V (.grid (i + 1) j)).rank < 2 * ((G.V (.grid (i + 1) (j + 1))).rank - p) := by
  intro D T L sc G W t i j hT M hM
  obtain ⟨e, Bs, Γ, X, om, om', hX, hY, -⟩ := hT M hM
  let w : InfinitePlace D.host.F := Classical.arbitrary _
  obtain ⟨hrs, A, hA⟩ := hY.geo.hV.sig w
  obtain ⟨τ, hτ, -⟩ := hX.cart w
  refine ⟨Γ.p, ⟨τ, ?_⟩, ?_⟩
  · have hJ : Γ.V.J.map (Bs.emb w).1 = (gramAt D (G.V (.grid (↑i + 1) (↑j + 1))) τ).map (starRingEnd ℂ) := by
      ext k l
      simp [hX.JW, hτ, gramAt]
    rw [hJ] at hA
    generalize gramAt D (G.V (.grid (↑i + 1) (↑j + 1))) τ = J at hA ⊢
    have h' : (A.map (starRingEnd ℂ))ᵀ * J * A = Matrix.fromBlocks 1 0 0 (-1) := by
      have := congrArg (fun Z => Z.map (starRingEnd ℂ)) hA
      simp only [Matrix.map_mul, Matrix.transpose_map] at this
      have e1 : (J.map (starRingEnd ℂ)).map (starRingEnd ℂ) = J := by ext; simp
      have e2 : (A.map star).map (starRingEnd ℂ) = A := by ext; simp
      have e3 : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p) (Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p) ℂ).map
          (starRingEnd ℂ) = Matrix.fromBlocks 1 0 0 (-1) := by
        ext (k | k) (l | l) <;> simp [Matrix.fromBlocks_map, Matrix.one_apply] <;> split_ifs <;> simp
      rw [e1, e2, e3] at this
      simpa only [Matrix.transpose_map] using this
    let f : Fin (G.V (.grid (↑i + 1) (↑j + 1))).rank ≃ Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p := (finSumFinEquiv.trans (finCongr hrs)).symm
    let P : Matrix (Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p) (Fin ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) ⊕ Fin Γ.p) ℂ := A.submatrix f.symm id
    have hP : Formalism.UG.cT (starRingEnd ℂ) P * J.reindex f f * P = Formalism.UG.Jpq ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p := by
      have : Formalism.UG.cT (starRingEnd ℂ) P = (A.map (starRingEnd ℂ))ᵀ.submatrix id f.symm := by
        ext k l; rfl
      rw [this, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h']
      rfl
    have hJJ : Formalism.UG.Jpq ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p * Formalism.UG.Jpq ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p = 1 := by
      simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
    have hl : (Formalism.UG.Jpq ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p * (Formalism.UG.cT (starRingEnd ℂ) P * J.reindex f f)) * P = 1 := by
      rw [Matrix.mul_assoc, hP, hJJ]
    exact ⟨f, ⟨P, _, mul_eq_one_comm.mp hl, hl⟩, hP⟩
  · have h1 := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin] at h1
    have h2 := hY.geo.lt
    have h3 := hY.geo.eBig
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spV₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spV] at h1 h2 h3
    omega

end GlobalTheory.FunObj
