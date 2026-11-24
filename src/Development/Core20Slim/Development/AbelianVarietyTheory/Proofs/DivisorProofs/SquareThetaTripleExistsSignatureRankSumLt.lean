module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
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
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
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

noncomputable section

namespace GlobalTheory.FunObj

theorem hasSignature_of_hasSig_conj {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (M.map (starRingEnd ℂ)) r s) : Formalism.UG.HasSignature M r s := by
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin n ≃ Fin r ⊕ Fin s := (finCongr hn.symm).trans finSumFinEquiv.symm
  let P : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := A.submatrix e.symm id
  have h2 := congrArg (fun X => X.map (starRingEnd ℂ)) hA
  simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.fromBlocks_map] at h2
  have hc : (starRingEnd ℂ) ∘ (starRingEnd ℂ) = id := funext fun z => Complex.conj_conj z
  have hc' : (starRingEnd ℂ) ∘ (star : ℂ → ℂ) = id := funext fun z => Complex.conj_conj z
  simp only [hc, hc', Matrix.map_id] at h2
  have key : (A.map (starRingEnd ℂ))ᵀ * M * A = Formalism.UG.Jpq r s := by
    rw [Formalism.UG.Jpq, h2]
    congr 1
    · ext a b; simp [Matrix.one_apply]
    · ext a b; simp
    · ext a b; simp
    · ext a b; simp [Matrix.one_apply]
  have key2 : Formalism.UG.cT (starRingEnd ℂ) P * Matrix.reindex e e M * P = Formalism.UG.Jpq r s := by
    rw [← key, Formalism.UG.cT, Matrix.reindex_apply]
    have hm : (A.submatrix e.symm id).map (starRingEnd ℂ) = (A.map (starRingEnd ℂ)).submatrix e.symm id := rfl
    simp only [P, hm, Matrix.transpose_submatrix]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  have hinv : (Formalism.UG.Jpq r s * (Formalism.UG.cT (starRingEnd ℂ) P * Matrix.reindex e e M)) * P = 1 := by
    rw [Matrix.mul_assoc, key2, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
    simp
  exact ⟨e, ⟨P, _, mul_eq_one_comm.mp hinv, hinv⟩, key2⟩

theorem squareTriple_sig_rank : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (hT : SquareTriple W t i j) (M : Vol G) (hM : M.Is t),
    ∃ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D (G.V (.grid (i + 1) (j + 1))) τ) ((G.V (.grid (i + 1) (j + 1))).rank - p) p) ∧
      (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank < 2 * ((G.V (.grid (i + 1) (j + 1))).rank - p) := by
  intro D T L sc G W t i j hT M hM
  obtain ⟨e, Bs, Γ, X, om, om', h, hTr, -⟩ := hT.of_forall hM
  refine ⟨Γ.p, ?_, ?_⟩
  · obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
    obtain ⟨τ, hτ, -⟩ := h.cart w
    refine ⟨τ, hasSignature_of_hasSig_conj ?_⟩
    have hs := hTr.geo.hV.sig w
    rw [h.JW, one_smul] at hs
    have hmap : (G.V (.grid (↑i + 1) (↑j + 1))).gram.map (Bs.emb w).1 = (gramAt D _ τ).map (starRingEnd ℂ) := by
      ext a b; simp [gramAt, hτ]
    rw [hmap] at hs
    exact hs
  · have hc := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin] at hc
    have hb := hTr.geo.eBig
    have hl := hTr.geo.lt
    dsimp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spW₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spV, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.spV₁] at hc hb hl
    show (G.V (.grid (↑i) (↑j + 1))).rank + (G.V (.grid (↑i + 1) ↑j)).rank < _
    omega

end GlobalTheory.FunObj

end
