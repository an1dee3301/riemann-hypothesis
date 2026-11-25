module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationHermitianLattice
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfHermEBijective
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHalfTr
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.GlobalProofs.EqZeroOfFourierCoefficientsVanish
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.Core20Slim.Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open GlobalTheory.CompanionTheory.HermPoisson

theorem hermCocompact (D : D7) (r : ℕ) :
    ∃ K : Set (hermA D r), IsCompact K ∧ ∀ x, ∃ l ∈ ratHerm D r, x - l ∈ K := by
  obtain ⟨-, K, hK, hKx⟩ := GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := r)
  refine ⟨K, hK, fun x => ?_⟩
  obtain ⟨γ, hγ, h⟩ := hKx x
  refine ⟨-γ, neg_mem hγ, ?_⟩
  rwa [sub_neg_eq_add, add_comm]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem hermFourierZero (D : D7) (r : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (lam : Measure (hermA D r)) (hH : lam.IsAddHaarMeasure) (𝓖 : Set (hermA D r))
    (h𝓖 : IsAddFundamentalDomain (ratHerm D r) 𝓖 lam) (φ : hermA D r → ℂ) (hφ : Continuous φ)
    (hper : ∀ x, ∀ l ∈ ratHerm D r, φ (x + l) = φ x)
    (hco : ∀ β : HermE D r,
      ∫ b in 𝓖, φ b * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D r r))) ∂lam = 0) :
    ∀ x, φ x = 0 := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : LocallyCompactSpace (Mx D r r) := i2
  haveI : SecondCountableTopology (Mx D r r) := i3
  haveI : T2Space (Mx D r r) := i4
  haveI : SecondCountableTopology (hermA D r) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D r) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : LocallyCompactSpace (hermA D r) :=
    (GlobalTheory.CompanionTheory.HermVol.isClosed_hermA (D := D) (r := r)).locallyCompactSpace
  haveI : Countable D.host.E := GlobalTheory.CompanionTheory.FourierComplete.countable_numberField D.host.E
  haveI : Countable (Matrix (Fin r) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin r → Fin r → D.host.E))
  have hmem : ∀ q : ratHerm D r, q.1.1 ∈ ratMx D r r := fun q => AddSubgroup.mem_comap.1 q.2
  haveI : Countable (ratHerm D r) := by
    choose g hg using fun q : ratHerm D r => mem_ratMx.1 (hmem q)
    exact Function.Injective.countable (f := g) fun a b h =>
      Subtype.ext (Subtype.ext (by rw [← hg a, ← hg b, h]))
  haveI := hH
  obtain ⟨K, hK, hc⟩ := hermCocompact D r
  intro x
  refine GlobalTheory.CompanionTheory.FourierComplete.eq_zero_of_coeffs_vanish (ratHerm D r) lam h𝓖 hK hc (T := ratHerm D r)
    (fun t b => chi ψ t.1.1 b) (fun t => continuous_chi hψ t.1.1) ?_ ?_ ?_ ?_ ?_ φ hφ hper ?_ x
  · intro t y l hl
    show chi ψ t.1.1 (y + l) = chi ψ t.1.1 y
    rw [chi_add_right, chi_rat hψ (hmem t) ⟨l, hl⟩, mul_one]
  · intro y
    exact chi_zero_left ψ y
  · intro s t y
    exact chi_add_left ψ s.1.1 t.1.1 y
  · intro t y
    show star (chi ψ t.1.1 y) = chi ψ (-t.1.1) y
    rw [chi_neg_left]
    exact star_psi' hψ _
  · intro a b hab
    refine rat_of_chi hψ (-a + b) fun t => ?_
    have h1 : chi ψ t.1.1 a * chi ψ t.1.1 (-a) = 1 := by
      rw [← chi_add_right, add_neg_cancel, chi_zero_right]
    rw [chi_add_right, ← hab t, mul_comm]
    exact h1
  · intro t
    obtain ⟨β, hβ⟩ := (ofHermE_bijective (D := D) (r := r)).2 t
    have h1 : ∀ b : hermA D r, chi ψ (-t).1.1 b =
        ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D r r))) := fun b => by
      show chi ψ (-t.1.1) b = _
      rw [chi_neg_left, ← hβ, ofHermE_val]
    simp only [h1]
    exact hco β

end PositivityTheory.Rg.Sw.Glob
