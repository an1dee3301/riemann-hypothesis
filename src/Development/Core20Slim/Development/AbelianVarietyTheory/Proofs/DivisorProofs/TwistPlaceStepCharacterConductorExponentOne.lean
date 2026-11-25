module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsMulOfCondExp
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedUnifAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Lemmas
public import Init.Data.Order.Lemmas
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

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
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TwistCond

theorem condExp_twist_eq_one : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      (Lc.C.mu0 j).UnrAt (GlobalTheory.AdelicU.splitPrime τ) → (G.ch.chiH (D.R.m - i)).UnrAt (GlobalTheory.AdelicU.splitPrime τ) →
      GlobalTheory.AdelicU.splitPrime τ ∈ Lc.Q t → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) = 1 := by
  intro D T Lc sc G μ₀ hL i j t v τ hmu hchi hQ
  set w := GlobalTheory.AdelicU.splitPrime τ with hw
  have hfun : chrW (GlobalTheory.SqStep.chs G i j t).ν τ =
      ((nuH G t i j).loc w).comp (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom) :=
    MonoidHom.ext fun x => GlobalTheory.SqStepArith.chrW_chs G hL i j t τ x
  have hloc : ∀ x, (nuH G t i j).loc w x =
      (Lc.C.mu0 j).loc w x * (Lc.xiH t).loc w x * ((G.ch.chiH (D.R.m - i)).loc w x)⁻¹ := by
    intro x
    show ((Lc.C.mu0 j * Lc.xiH t) * (G.ch.chiH (D.R.m - i))⁻¹).loc w x = _
    rfl
  have h1 : GlobalTheory.SplitFlip.CondLE (unifAt v) 1 (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) := by
    rw [hfun, GlobalTheory.CondLESplit.condLE_iff]
    intro x hx hx1
    rw [hloc, hmu x hx, hchi x hx, hL.xi_tame t w x hx hx1]
    simp
  have h0 : ¬ GlobalTheory.SplitFlip.CondLE (unifAt v) 0 (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) := by
    rw [hfun, GlobalTheory.CondLESplit.condLE_iff]
    intro h
    apply (hL.Q_ram t w).2 (Or.inl hQ)
    intro x hx
    have hle : Valued.v ((x : w.adicCompletion D.host.E) - 1) ≤ WithZero.exp (-((0 : ℕ) : ℤ)) := by
      simp only [Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact Valuation.map_sub_le _ (le_of_eq hx) (by simp)
    have := h x hx hle
    rw [hloc, hmu x hx, hchi x hx] at this
    simpa using this
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp
  have hne : ({c | GlobalTheory.SplitFlip.CondLE (unifAt v) c (chrW (GlobalTheory.SqStep.chs G i j t).ν τ)} : Set ℕ).Nonempty := ⟨1, h1⟩
  apply le_antisymm (Nat.sInf_le h1)
  rw [Nat.one_le_iff_ne_zero]
  intro h
  have := Nat.sInf_mem hne
  rw [h] at this
  exact h0 this

end GlobalTheory.TwistCond
