module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceNonsplitPlaceStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelLeviDeterminantIntegralSelfDualLatticeStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelicStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatSmulSingle
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Core.Rk.SphSec

section Gen

variable {G : Type} [Group G] (P K : Subgroup G) (f : P →* ℂ)

theorem gen_wd (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (p p' : P) (k k' : G) (hk : k ∈ K) (hk' : k' ∈ K)
    (e : (p : G) * k = p' * k') : f p = f p' := by
  have h1 : ((p'⁻¹ * p : P) : G) = k' * k⁻¹ := by
    have : (p : G) = p' * (k' * k⁻¹) := by rw [← mul_assoc, ← e, mul_inv_cancel_right]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, this, inv_mul_cancel_left]
  have h2 := hK _ (h1 ▸ mul_mem hk' (inv_mem hk))
  calc f p = f (p' * (p'⁻¹ * p)) := by rw [mul_inv_cancel_left]
    _ = f p' := by rw [map_mul, h2, mul_one]

variable (hI : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k)

noncomputable def genFun (g : G) : ℂ := f (hI g).choose

variable {P K f hI}

theorem genFun_mul (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (p : P) {k : G} (hk : k ∈ K) :
    genFun P K f hI (p * k) = f p := by
  obtain ⟨k', hk', e⟩ := (hI (p * k)).choose_spec
  exact gen_wd P K f hK _ _ _ _ hk' hk e.symm

theorem genFun_right (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (g : G) {k : G} (hk : k ∈ K) :
    genFun P K f hI (g * k) = genFun P K f hI g := by
  obtain ⟨k₀, hk₀, e⟩ := (hI g).choose_spec
  conv_lhs => rw [e, mul_assoc]
  exact genFun_mul hK _ (mul_mem hk₀ hk)

theorem genFun_left (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (p : P) (g : G) :
    genFun P K f hI (p * g) = f p * genFun P K f hI g := by
  obtain ⟨k₀, hk₀, e⟩ := (hI g).choose_spec
  conv_lhs => rw [e, ← mul_assoc]
  rw [← Subgroup.coe_mul, genFun_mul hK _ hk₀, map_mul]
  rfl

theorem genFun_one (hK : ∀ p : P, (p : G) ∈ K → f p = 1) : genFun P K f hI 1 = 1 := by
  have := genFun_mul (hI := hI) hK 1 (one_mem K)
  rwa [Subgroup.coe_one, mul_one, map_one] at this

theorem genFun_unique (Ψ : G → ℂ) (hΨ : ∀ (p : P) g, Ψ (p * g) = f p * Ψ g) (hΨK : ∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g)
    (g : G) : Ψ g = Ψ 1 * genFun P K f hI g := by
  obtain ⟨k₀, hk₀, e⟩ := (hI g).choose_spec
  have := hΨ (hI g).choose 1
  rw [mul_one] at this
  rw [genFun, mul_comm]
  conv_lhs => rw [e]
  rw [hΨK _ hk₀, this]

theorem continuous_genFun [TopologicalSpace G] [IsTopologicalGroup G] (hK : ∀ p : P, (p : G) ∈ K → f p = 1)
    (ho : IsOpen (K : Set G)) : Continuous (genFun P K f hI) := by
  refine continuous_iff_continuousAt.2 fun g => (continuousAt_const (y := genFun P K f hI g)).congr ?_
  filter_upwards [(ho.preimage (continuous_const_mul g⁻¹)).mem_nhds (by simp [one_mem])] with h hh
  have := genFun_right (hI := hI) hK g (k := g⁻¹ * h) hh
  rwa [mul_inv_cancel_left, eq_comm] at this

theorem gen_exists [TopologicalSpace G] [IsTopologicalGroup G] (P K : Subgroup G) (f : P →* ℂ)
    (hI : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (ho : IsOpen (K : Set G)) :
    ∃ φ : G → ℂ, (∀ (p : P) g, φ (p * g) = f p * φ g) ∧ Continuous φ ∧ (∀ g, ∀ k ∈ K, φ (g * k) = φ g) ∧ φ 1 = 1 ∧
      ∀ Ψ : G → ℂ, (∀ (p : P) g, Ψ (p * g) = f p * Ψ g) → (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∀ g, Ψ g = Ψ 1 * φ g :=
  ⟨genFun P K f hI, genFun_left hK, continuous_genFun hK ho, fun g _ hk => genFun_right hK g hk, genFun_one hK,
    fun Ψ hΨ hΨK g => genFun_unique Ψ hΨ hΨK g⟩

end Gen


set_option maxHeartbeats 1000000 in
theorem exists_isSphSecAt_unique : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ v : FinPl D, (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt μ w) → ∀ s : ℂ, ∃ φ, IsSphSecAt A L v μ s φ ∧ ∀ Ψ : Gv (dblSp A) v → ℂ, (∀ (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram) g, Ψ (p * g) = charAt μ v (aH _ D.sp.cm.sig (dblSp A).gram p) * npow (absEv D.host.F D.host.E v (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) * Ψ g) → (∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram L v, ∀ g, Ψ (g * k) = Ψ g) → ∀ g, Ψ g = Ψ 1 * φ g := by
  intro D A L hL μ hμ v hunr s
  haveI : Submodule.IsFullLattice D.host.E L :=
    Formalism.IndefR.Fin.PDA.selfDual_isFullLattice A L hL
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (KFin D.sp.cm.sig (dblSp A).gram L v) := by
    by_cases hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v
    · exact GlobalTheory.T.hasIwasawaDecomposition_doubled_split_place D A L hL v hs
    · exact GlobalTheory.T.iwasawa_doubled_hermitian_space_nonsplit_place D A L hL v hs
  let N : ℝ≥0 →* ℂ := ⟨⟨fun r => npow r (s + (A.rank : ℂ) / 2), one_npow _⟩, fun r r' => GlobalTheory.Doubling.npow_mul r r' _⟩
  let f : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram →* ℂ :=
    (Circle.coeHom.comp ((charAt μ v).comp (aH _ D.sp.cm.sig (dblSp A).gram))) *
      (N.comp ((absEv D.host.F D.host.E v).comp (aH _ D.sp.cm.sig (dblSp A).gram)))
  have hf : ∀ p, f p = (charAt μ v (aH _ D.sp.cm.sig (dblSp A).gram p) : ℂ) *
      npow (absEv D.host.F D.host.E v (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) := fun p => rfl
  have hK : ∀ p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram,
      (p : Gv (dblSp A) v) ∈ KFin D.sp.cm.sig (dblSp A).gram L v → f p = 1 := by
    intro p hp
    have h1 := GlobalTheory.T.siegelLeviDeterminant_integral_selfDual_lattice D A L hL v p hp
    have h2 : (((aH _ D.sp.cm.sig (dblSp A).gram p)⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) :
        Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v := by
      rw [← map_inv]
      exact GlobalTheory.T.siegelLeviDeterminant_integral_selfDual_lattice D A L hL v p⁻¹ (inv_mem hp)
    rw [hf, GlobalTheory.T.ideleCharacter_eq_one_integral_units_unramified_adelic D μ v _ h1 h2 hunr,
      abs_aH_eq_one (continuous_absEv v) (isCompact_KFin v) p hp, one_npow, Circle.coe_one, one_mul]
  clear_value f
  obtain ⟨φ, hl, hc, hr, h1, hu⟩ := gen_exists (G := Gv (dblSp A) v) _ _ f hI hK (isOpen_KFin v)
  refine ⟨φ, ⟨mem_degPSH.2 ⟨fun p g => by rw [hl, hf], hc, IsKFinite.of_invariant fun g k hk => hr g k hk⟩,
    fun k hk g => hr g k hk, h1⟩, fun Ψ hΨ hΨK g => hu Ψ (fun p g => by rw [hΨ, hf]) hΨK g⟩

end GlobalTheory.Core.Rk.SphSec

end
