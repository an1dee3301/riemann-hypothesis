module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsBiSmooth
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.Core20Slim.Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMultTOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Prod.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Topology.Defs.Filter

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

open scoped ComplexOrder

theorem sig_eq_of_definite {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef ∨ (-G).PosDef) {p q : ℕ}
    (h : Formalism.UG.HasSignature G p q) : (p, q) = (n, 0) ∨ (p, q) = (0, n) := by
  rcases hG with hG | hG
  · exact Or.inl (GlobalTheory.DefLiftMult.sig_of_posDef hG h)
  · right
    obtain ⟨hn, Q, hQ⟩ := Formalism.UG.P.sig_data G p q h
    have hp : p = 0 := by
      by_contra hp
      have i : Fin p := ⟨0, Nat.pos_of_ne_zero hp⟩
      have h1 := (hG.posSemidef.conjTranspose_mul_mul_same Q).diag_nonneg (i := Sum.inl i)
      rw [Matrix.mul_neg, Matrix.neg_mul, hQ] at h1
      simp [Formalism.UG.Jpq] at h1
      exact absurd h1 (by norm_num)
    subst hp
    simp at hn
    rw [hn]

theorem isDefinite_of_defSp {D : D7} {A : HSp D} (x : DefSp A) (hx : x.Is) : A.IsDefinite := by
  have hτ : ∀ τ, (gramAt D A τ).PosDef ∨ (-(gramAt D A τ)).PosDef := by
    intro τ
    have hp := (hx.cart τ).2.2
    rcases hx.pm τ with h | h
    · left
      rwa [h, Matrix.mul_one] at hp
    · right
      rwa [h, Matrix.mul_neg, Matrix.mul_one] at hp
  intro σ
  have hs := hx.sig σ
  have key : (A.sig σ).1 = A.rank ∧ (A.sig σ).2 = 0 ∨ (A.sig σ).1 = 0 ∧ (A.sig σ).2 = A.rank := by
    obtain ⟨τ, rfl | rfl⟩ := GlobalTheory.DefLiftMult.exists_tauE D σ
    · simpa [Prod.ext_iff] using sig_eq_of_definite (hτ τ) hs
    · have e : A.gram.map ((starRingEnd ℂ).comp (tauE D τ)) = (gramAt D A τ)ᴴᵀ := by
        ext i j
        rfl
      rw [e] at hs
      have hd : ((gramAt D A τ)ᴴᵀ).PosDef ∨ (-(gramAt D A τ)ᴴᵀ).PosDef := by
        rcases hτ τ with h | h
        · exact Or.inl h.conjTranspose.transpose
        · right
          have := h.conjTranspose.transpose
          rwa [Matrix.conjTranspose_neg, Matrix.transpose_neg] at this
      simpa [Prod.ext_iff] using sig_eq_of_definite hd hs
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (Prod.ext h1 h2)
  · exact Or.inr (Prod.ext h1 h2)

theorem isCompact_ginfC_of_defSp : ∀ (D : D7) (A : HSp D) (x : DefSp A), x.Is → IsCompact (GinfC A : Set (GA D A)) :=
  fun _ _ x hx => Formalism.IndefR.Eqv.isCompact_GinfC hx.sig (isDefinite_of_defSp x hx)

end GlobalTheory.SeeSaw

end
