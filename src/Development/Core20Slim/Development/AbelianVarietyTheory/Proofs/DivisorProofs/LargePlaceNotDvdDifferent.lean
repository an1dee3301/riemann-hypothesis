module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.Core20Slim.Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NotDvdDiff
public import Batteries.Classes.RatCast
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalRingCardinality.DataParamsT
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
public import Formalism.SharpRestriction.ElevenLe
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.OreLocalization.OreSet
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.Locus

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop

namespace GlobalTheory.DiffSOne

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem not_dvd_diff_of_split (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {p : ℕ} (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 L)).ncard = Module.finrank ℚ L)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 K) := by
  have h' : ({w : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ w.asIdeal}).ncard = Module.finrank ℚ L := by
    rw [← h, Formalism.L2.SG.Pf.TypedLoc.primesOver_eq L hp]
    exact (Set.ncard_image_of_injective _ fun v w hvw => HeightOneSpectrum.ext hvw).symm
  obtain ⟨he, -⟩ := Formalism.L2.SG.Pf.TypedLoc.tower_ef K L hp h' v hv
  have hvq : v.asIdeal ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
    rw [Formalism.L2.SG.Pf.TypedLoc.primesOver_eq K hp]; exact ⟨v, hv, rfl⟩
  have : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := hvq.2
  have : v.asIdeal.IsPrime := v.isPrime
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp)] at he
  rw [not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain]
  exact he

theorem not_dvd_differentIdeal : ∀ {D : D7} (large₂ : SizeData₂ D), Rec large₂ → ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ∈ S1 D →
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  intro D large₂ hR v hv
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
  rcases (S1_mem_OmF D).1 hv with h | h | h | h
  · exact Formalism.L2.SG.Pf.FibD.not_dvd_diff v 0 h
  · exact Formalism.L2.SG.Pf.FibD.not_dvd_diff v 1 h
  · exact not_dvd_diff_of_split D.host.F D.host.E D.host.pde_prime Pm.pde_split.1 v h
  · exact not_dvd_diff_of_split D.host.F D.host.E D.host.pde'_prime Pm.pde_split.2 v h

end GlobalTheory.DiffSOne
