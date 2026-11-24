module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Prelude
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.Nonempty
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Sets.Compacts

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.VolExist

theorem nonempty_vol {D : D7} (V : HSp D) : Nonempty (Vol V) := by
  obtain ⟨i1, i2, i3, i4, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨-, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V
    (Measure.haar : Measure (GA D V)) inferInstance
  exact ⟨⟨Measure.haar, 𝓕, inferInstance, h𝓕⟩⟩

theorem nonempty_volN {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : Nonempty (VolN d) :=
  let ⟨ν, 𝓝, h⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D S ρ d.e (isIsoSub_e d)
  ⟨⟨ν, 𝓝, h⟩⟩

theorem nonempty_volM (D : D7) (m n : ℕ) : Nonempty (VolM D m n) :=
  let ⟨μ, 𝓕, h⟩ := exists_isCovolOne D m n
  ⟨⟨μ, 𝓕, h⟩⟩

theorem nonempty_volU (D : D7) (ρ : ℕ) : Nonempty (VolU D ρ) :=
  let ⟨ν, h⟩ := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).1
  ⟨⟨ν, h⟩⟩

theorem measures_exist : ∀ D : D7, (∀ V : HSp D, Nonempty (Vol V)) ∧
    (∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), Nonempty (VolN d)) ∧ (∀ m n, Nonempty (VolM D m n)) ∧
    ∀ ρ, Nonempty (VolU D ρ) :=
  fun D => ⟨nonempty_vol, fun _ _ _ d => nonempty_volN d, nonempty_volM D, nonempty_volU D⟩

end GlobalTheory.Unf.VolExist

end
