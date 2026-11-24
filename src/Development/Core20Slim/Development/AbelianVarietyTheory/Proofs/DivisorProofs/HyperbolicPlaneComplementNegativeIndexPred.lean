module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneSplit
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryPosDefHermitianSameRank
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.List.FinRange
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaneComplementSig

open Matrix

theorem hasSignature_plane : Formalism.UG.HasSignature (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
  refine GlobalTheory.FrameComplement.hasSignature_of_frame (by simp)
    (Matrix.of fun i k => Sum.elim (fun _ => ![1, 1 / 2] i) (fun _ => ![1, -1 / 2] i) k) ?_
  ext (a | a) (b | b) <;> fin_cases a <;> fin_cases b <;>
    simp [Formalism.UG.Jpq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, map_ofNat] <;> norm_num

theorem sig : ∀ (D : D7) (S S₁ : HSp D) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V) (q : ℕ), S.rank = S₁.rank + 2 →
    Formalism.BasicNotions.HSpace.IsIsomEmb S₁ S ι → S.hT x x = 0 → S.hT y y = 0 → S.hT x y = 1 →
    (∀ u, S.hT x (ι u) = 0 ∧ S.hT y (ι u) = 0) → NegIdx S (q + 1) →
    ∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature (S₁.gram.map τ) (S₁.rank - q) q := by
  intro D S S₁ ι x y q hr hι hxx hyy hxy ho hneg τ
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ

  have hS : Formalism.UG.HasSignature (S.gram.map τ) (S.rank - (q + 1)) (q + 1) := by
    obtain ⟨ρ, hσ | hσ⟩ := GlobalTheory.DefiniteMult.exists_tauE_or_conj D τ
    · subst hσ
      simpa [gramAt] using hneg ρ
    · subst hσ
      have h1 := GlobalTheory.BottomIsom.hasSignature_map_star (by simpa [gramAt] using hneg ρ)
      rw [Matrix.map_map] at h1
      exact h1
  obtain ⟨⟨a, b⟩, h₁⟩ := GlobalTheory.WittLow.exists_sig S₁ τ
  have c₁ := (Formalism.UG.P.sig_data _ _ _ h₁).1
  have cS := (Formalism.UG.P.sig_data _ _ _ hS).1
  simp only [Fintype.card_fin] at c₁ cS
  let v : Fin S₁.rank ⊕ Fin 2 → S.V := Sum.elim (fun i => ι (S₁.frame i)) ![x, y]
  have hyx : S.hT y x = 1 := by
    have h := S.herm.eq x y
    rw [hxy, map_one] at h
    exact h.symm
  have hv : (Matrix.of fun k l => S.hT (v k) (v l)) =
      fromBlocks S₁.gram 0 0 (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) D.host.E) := by
    ext (i | i) (j | j)
    · simp only [v, Matrix.of_apply, fromBlocks_apply₁₁, Sum.elim_inl, HSpace.gram]; exact hι _ _
    · fin_cases j
      · have h := S.herm.eq x (ι (S₁.frame i))
        rw [(ho _).1, map_zero] at h
        simp [v, ← h]
      · have h := S.herm.eq y (ι (S₁.frame i))
        rw [(ho _).2, map_zero] at h
        simp [v, ← h]
    · fin_cases i
      · simpa [v] using (ho _).1
      · simpa [v] using (ho _).2
    · fin_cases i <;> fin_cases j <;> simp [v, hxx, hyy, hxy, hyx]
  have hF : Formalism.UG.HasSignature ((Matrix.of fun k l => S.hT (v k) (v l)).map τ) (a + 1) (b + 1) := by
    rw [hv, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero τ), Matrix.map_zero _ (map_zero τ)]
    have e : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) D.host.E).map τ = !![0, 1; 1, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [e]
    exact GlobalTheory.FrameComplement.hasSignature_fromBlocks h₁ hasSignature_plane
  have key := Formalism.BasicNotions.sig_family S τ hτ v hF hS
  have hb : b = q := by omega
  have ha : a = S₁.rank - q := by omega
  subst hb ha
  exact h₁

end GlobalTheory.PlaneComplementSig
