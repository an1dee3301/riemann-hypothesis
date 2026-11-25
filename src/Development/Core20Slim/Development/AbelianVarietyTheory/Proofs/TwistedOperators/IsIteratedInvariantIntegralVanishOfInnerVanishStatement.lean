module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIteratedInvariantIntegralVanishOfInnerVanish
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIteratedInvariantIntegral_vanish_of_inner_vanish : ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, SecondCountableTopology (H i)] [∀ i, LocallyCompactSpace (H i)] [∀ i, T2Space (H i)] [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)] (A B R K : ∀ i, Subgroup (H i)) (l : List ι), l.Nodup → (∀ i ∈ l, Split (A i) (B i) (R i) (K i)) → ∀ (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (ρ' : ∀ i, Measure ((R i).subgroupOf (B i))) (μ' : ∀ i, Measure (B i)), (∀ i ∈ l, (ρ i).IsHaarMeasure ∧ (μ i).IsHaarMeasure ∧ (ρ' i).IsHaarMeasure ∧ (μ' i).IsHaarMeasure) → ∀ (S : Finset (∀ i, H i)) (q : (∀ i, H i) → ℂ) (z : ℂ), (∀ b ∈ S, ∀ i, b i ∈ B i) → BiInv R K l q → (∀ h, (∀ i, i ∉ l → h i = 1) → q h ≠ 0 → ∃ b ∈ S, InCells A R K l b h) → NIter ρ μ q l 1 z → (∀ a : ∀ i, H i, (∀ i, a i ∈ A i) → (∀ i, i ∉ l → a i = 1) → NIter ρ' μ' (fun b : ∀ i, B i => q fun i => a i * (b i).1) l 1 0) → z = 0 := by
  first | exact @GlobalTheory.NestVan.nested_vanish | exact GlobalTheory.NestVan.nested_vanish | (intros; apply GlobalTheory.NestVan.nested_vanish <;> assumption)
