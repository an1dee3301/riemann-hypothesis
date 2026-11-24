module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CondEIsCoprimeHalfDifferent
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
public import Batteries.Classes.RatCast
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataKernels
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalRingCardinality.DataParamsT
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.HostCls
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.ElevenLe
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Coprime
public import Init.Data.Nat.Div.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.StdPairPlaces

theorem coprime_of_splitK {φ : Formalism.HC.Frame} {H : Formalism.HC.HostRaw φ} {p : ℕ} (hp : p.Prime)
    (h : primeClass H p = PrimeClass.splitK) : Nat.Coprime p (H.QS * H.q * H.d) := by
  have hn : ¬ p ∣ H.condN := not_dvd_of_splitK hp h
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 hn

theorem natCast_two_q_d_notMem : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.SqTop.Rec large₂ → ∀ {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T},
    L.Is μ₀ → ∀ (t : T), ∀ w ∈ locPl G t, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  intro D large₂ hR T L sc G μ₀ hL t w hw
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
  have hsp : ∀ p : ℕ, p.Prime → p ∈ D.host.levelPrimes → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp h =>
    coprime_of_splitK hp (Pm.level_split p h)
  have hdvd : D.host.QS * D.host.q * D.host.d ∣ LevelStarExponents.condE D := dvd_rfl
  rcases GlobalTheory.FunObj.Good.locPl_cases hw with ⟨a, -⟩ | ⟨-, -, b⟩
  · rcases G.pl.mem_S0_of_sum_eq.1 a with a | a
    · refine GlobalTheory.HalfCompare.not_mem_of_coprime w (b := q0 D) ?_ ((GlobalTheory.FunObj.Good.natCast_mem_under w _).1 (a ▸ G.pl.basePlace_over_qZero))
      exact (GlobalTheory.FunObj.StdDatum.HalfDiff.coprime_of_mod (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1 (hdvd.mul_left _)).symm
    · simp only [S1_mem_OmF, GlobalTheory.FunObj.Good.natCast_mem_under] at a
      rcases a with a | a | a | a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w
          (GlobalTheory.FunObj.StdDatum.HalfDiff.coprime_of_mod (D.ntypes.g_cond 0) dvd_rfl).symm a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w
          (GlobalTheory.FunObj.StdDatum.HalfDiff.coprime_of_mod (D.ntypes.g_cond 1) dvd_rfl).symm a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w (hsp _ D.host.pde_prime D.host.pde_level.1).symm a
      · exact GlobalTheory.HalfCompare.not_mem_of_coprime w (hsp _ D.host.pde'_prime D.host.pde_level.2).symm a
  · exact fun h => (hL.Q_off t w b).1 (GlobalTheory.HalfCompare.mem_of_dvd h ⟨D.sp.T, by ring⟩)

end GlobalTheory.StdPairPlaces

end
