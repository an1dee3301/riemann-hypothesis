module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryCharacterTrivialAtNonsplitPlace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCharEqOneOfForallCircleCharStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppInertUnitaryAdelicPointComponentAtPrimesStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertSupportedUnitaryPointIntegralCofiniteStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPrimeComponentFinsetProdStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonSplitSupportedFinitePartIntegralInertStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProdLocalComponentsEqPrimePartStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.List.Basic
public import Init.Data.List.Lemmas
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertSuppChar

theorem eq_one_at_inert {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (μ : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* Circle)
    (hμ : ∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppInert D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
      Formalism.MainNotions.StandardLatticesGL3.IntG D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → μ k = 1)
    {q : ℕ} (hq : q.Prime) (hi : Formalism.MainNotions.StandardLatticesGL3.InertQ D q) (y : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) :
    μ (GlobalTheory.NormSum.VacInt.part D (fun p => p = q) y) = 1 := by
  obtain ⟨g, hg⟩ := GlobalTheory.BotFormula.exists_isFinPt_of_gram_one V hG y rfl
  rw [← GlobalTheory.BotClassDict.finStd_of_isFinPt V hG hg]
  obtain ⟨l, hl, e⟩ := GlobalTheory.T.exists_prod_localComponents_eq_primePart V hG q hq g
  rw [← e, map_list_prod, map_list_prod, List.map_map]
  refine List.prod_eq_one (M := Circle) fun z hz => ?_
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hz
  obtain ⟨v, ε, hε, hqv, hs⟩ := hl h hh
  have hn : GlobalTheory.WeilParts.NonSplitAt D v ε := (GlobalTheory.InertPlace.inertQ_iff_nonSplitAt D q hq v ε hε hqv).1 hi
  refine GlobalTheory.InertChar.char_eq_one_of_nonSplit D V _
    (GlobalTheory.NormRatio.SphCoset.isSelfDualC_of_gram_one hG (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D V.rank)) v ε hn
    (μ.comp (GlobalTheory.BotClassDict.finStd V hG)) (fun k hk hst => ?_) h hs
  obtain ⟨a1, a2⟩ := GlobalTheory.T.nonSplitSupported_finitePart_integral_inert V hG v ε hn k hk hst
  exact hμ _ a1 a2

theorem char_eq_one : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D), V.gram = 1 → ∀ (ν : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* ℂˣ),
  (∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → ν k = 1) →
  (∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppInert D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
    Formalism.MainNotions.StandardLatticesGL3.IntG D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → ν k = 1) →
  ∀ x, ν x = 1 := by
  intro D V hG ν hs hi x
  refine GlobalTheory.T.eq_one_of_forall_circle_char_eq_one ν x fun μ hμ => ?_
  rw [← GlobalTheory.NormSum.VacInt.part_mul_compl D (fun q => ¬ Formalism.MainNotions.StandardLatticesGL3.InertQ D q) x, map_mul,
    hμ _ (hs _ (GlobalTheory.NormSum.VacInt.suppSplit_part D x)), one_mul]
  have hy := GlobalTheory.NormSum.VacInt.suppInert_part D x
  generalize GlobalTheory.NormSum.VacInt.part D (fun q => ¬¬Formalism.MainNotions.StandardLatticesGL3.InertQ D q) x = y at hy ⊢
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.T.inertSupportedUnitaryPoint_integral_cofinite y hy
  rw [← GlobalTheory.NormSum.VacInt.part_mul_compl D (fun p => p ∈ s) y, map_mul,
    hμ _ (hi _ (GlobalTheory.T.suppInert_unitaryAdelicPointComponentAtPrimes _ _ hy) hs2), mul_one]
  have hloc : ∀ q, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → μ (GlobalTheory.NormSum.VacInt.part D (fun p => p = q) y) = 1 :=
    fun q hq hqi => eq_one_at_inert V hG μ (fun k a1 a2 => hμ _ (hi k a1 a2)) hq hqi y
  clear hs2
  induction s using Finset.induction_on with
  | empty => rw [(GlobalTheory.T.unitaryPrimeComponent_finset_prod y).1, map_one]
  | insert q s hq ih =>
    rw [(GlobalTheory.T.unitaryPrimeComponent_finset_prod y).2 q s hq, map_mul, hloc q (hs1 q (Finset.mem_insert_self q s)).1
      (hs1 q (Finset.mem_insert_self q s)).2, one_mul]
    exact ih fun p hp => hs1 p (Finset.mem_insert_of_mem hp)

end GlobalTheory.InertSuppChar
