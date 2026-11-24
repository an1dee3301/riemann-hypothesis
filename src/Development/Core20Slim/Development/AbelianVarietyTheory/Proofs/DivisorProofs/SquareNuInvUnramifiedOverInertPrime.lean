module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaTildeHeckeCharSplitMulSignOfNormFormula
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.JointCharacters.LocEMulLocE
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.SqNum

theorem nuH_inv_unrAt_of_inertQ : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m) (P : HeightOneSpectrum (𝓞 D.host.E)), (∃ q : ℕ, q.Prime ∧ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) → (nuH G μ₀ i j)⁻¹.UnrAt P := by
  intro D T L sc μ₀ hL G i j P hq
  obtain ⟨q, hqp, hqi, hqP⟩ := hq

  have hmu : (L.C.mu0 j).UnrAt P := (L.C.isMu0 j).unr P fun k hk => by
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hk
    have e := prime_unique (K := D.host.E) hqp (D.host.g_prime k) hqP hk'
    exact GlobalTheory.Mem.Col2.SplitChar.not_inertQ_g k (e ▸ hqi)

  have hchi : (G.ch.chiH (D.R.m - i)).UnrAt P := by
    refine G.ch.unr (D.R.m - i) (by omega) (by omega) P fun hv => ?_
    obtain ⟨e, he⟩ := G.pl.w_split _ hv
    have hov := G.pl.w_over _ hv
    set w := G.pl.w (P.under (𝓞 D.host.F))
    have h1 : ((q : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (q : 𝓞 D.host.F) ∈ P.asIdeal
      simpa using hqP
    rw [← hov] at h1
    have hqw : ((q : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
      have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (q : 𝓞 D.host.F) ∈ w.asIdeal := h1
      simpa using h2
    have hfix := hqi _ w.isPrime w.ne_bot hqw
    obtain ⟨⟨e1, e2, v, ε, hε, e3⟩, e4⟩ := he
    exact GlobalTheory.DualPairCheck.split_ne e ⟨e1, e2, v, ε, hε, e3⟩
      (GlobalTheory.EtaProduct.cA_of_fixed ⟨e1, ⟨v, ε, hε, Or.inl ⟨e2, e3⟩⟩, e4⟩ hfix)
  have e : nuH G μ₀ i j = L.C.mu0 j * (G.ch.chiH (D.R.m - i))⁻¹ := by
    rw [nuH, hL.xi_base, mul_one, div_eq_mul_inv]
  rw [e]
  exact (hmu.mul hchi.inv).inv

end GlobalTheory.FunObj.SqNum
