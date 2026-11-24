module

public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FunKit
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeUNuInv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBetaInvHeckeU
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeUAlphaH
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapFinPartILocFEq
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOfOrderDvd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairBigMemberTwistedTupleStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairSmallMemberTwistedTupleStatement
public import Batteries.Classes.RatCast
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalRingCardinality.DataParamsT
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.ElevenLe
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.SqTop.BotT

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}

theorem nuH_eq (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) :
    nuH G t i j = nuH G μ₀ i j * L.xiH t := by
  simp only [nuH, hL.xi_base, mul_one]
  exact mul_div_right_comm _ _ _

theorem alphaH_eq (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) :
    alphaH L t i j = alphaH L μ₀ i j * L.xiH t := by
  simp only [alphaH, hL.xi_base, mul_one]
  exact mul_right_comm _ _ _

theorem exists_heckeU_nuInv (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) :
    ∃ χ : HeckeU D (botBig D i j + botSmall D i j), (∀ x, χ.f x = (nuH G t i j)⁻¹.1 (finIdl D x)) ∧
      ∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χ.n τ := by
  obtain ⟨χ₀, h₀, hw⟩ := GlobalTheory.BottomNu.exists_heckeU_nu_inv hL G i j
  obtain ⟨ξ, hξ, hn⟩ := GlobalTheory.XiSplit.exists_heckeU_xi hL t
  refine ⟨GlobalTheory.AlphaSplit.mulU _ χ₀ (GlobalTheory.AlphaSplit.invU ξ) (by simp), fun x => ?_, fun τ => ?_⟩
  · rw [GlobalTheory.AlphaSplit.mulU_f, GlobalTheory.AlphaSplit.invU_f, h₀, hξ, nuH_eq hL G t, mul_inv]
    rfl
  · show _ ≤ χ₀.n τ + -ξ.n τ
    rw [hn, neg_zero, add_zero]; exact hw τ

theorem exists_heckeU_alpha (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) :
    ∃ χ : HeckeU D (botSmall D i j), ∀ x, χ.f x = (alphaH L t i j).1 (finIdl D x) := by
  obtain ⟨χ₀, h₀⟩ := GlobalTheory.FunObj.SqNum.exists_heckeU_alphaH hL G i j
  obtain ⟨ξ, hξ, -⟩ := GlobalTheory.XiSplit.exists_heckeU_xi hL t
  refine ⟨GlobalTheory.AlphaSplit.mulU _ χ₀ ξ (by simp), fun x => ?_⟩
  rw [GlobalTheory.AlphaSplit.mulU_f, h₀, hξ, alphaH_eq hL t]
  rfl

theorem pde_ne_q {large₂ : Formalism.BasicNotions.SizeData₂ D} (hR : GlobalTheory.SqTop.Rec large₂) : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) := by
  obtain ⟨⟨P, -, -⟩, -⟩ := hR.size
  have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
  exact ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩

end GlobalTheory.SqTop.BotT

namespace GlobalTheory.SqTop

theorem botExT_holds (hI : ∀ D, GlobalTheory.NormSum.Inp D) : BotExT := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro δ t0 Q P t i j
  obtain ⟨hq, hq'⟩ := BotT.pde_ne_q hR
  obtain ⟨χν, hν, hw⟩ := BotT.exists_heckeU_nuInv hL G t i j
  obtain ⟨χβ, hβ⟩ := GlobalTheory.FunObj.SqNum.exists_betaInv_heckeU hL G i j
  obtain ⟨χα, hα⟩ := BotT.exists_heckeU_alpha hL G t i j
  obtain ⟨P₁, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_bottomPair_bigMember_twisted_tuple (hI D) hL hq hq' G t P.crv P.pt0 i j χβ hβ χν hν hw
  obtain ⟨P₂, h1', h2', h3', h4', h5'⟩ := GlobalTheory.T.exists_bottomPair_smallMember_twisted_tuple (hI D) hL hq hq' G t P.crv P.pt0 i j χα hα χν hν hw
  exact ⟨P₁, P₂, ⟨⟨h1, h1', h2, h2'.trans h2.symm⟩, h3, h3', h4, h4', ⟨h5, h5'⟩⟩⟩

end GlobalTheory.SqTop

end
