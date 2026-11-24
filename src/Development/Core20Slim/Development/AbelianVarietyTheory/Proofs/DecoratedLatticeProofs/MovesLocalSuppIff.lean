module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

namespace GlobalTheory.FinPl

theorem movesLocal_supp_iff {D : D7} (S : HSp D) (L : Lat S) (hL : Submodule.IsLattice D.host.E L) (v : Pl D)
    (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ latV S L (fun _ => True) ↔ y ∈ latV S L (· = v) := by
  have hT := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (fun _ => True)).2 S).2.2.2 L y hL
  have hV := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).2 S).2.2.2 L y hL
  have hsub : ∀ i, y i ∈ idAt D (fun _ => True) := by
    intro i
    have h := hy i
    simp only [idAt, Submodule.mem_inf] at h ⊢
    refine ⟨h.1, ?_⟩
    simp only [Submodule.mem_iInf]
    intro w
    exact absurd trivial w.2
  rw [hT, hV]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨hy, fun w hw e he => h w trivial e he⟩
  · rintro ⟨_, h⟩
    refine ⟨hsub, fun w _ e he => ?_⟩
    by_cases hwv : w = v
    · exact h w hwv e he
    · obtain ⟨ε, -, -, -, hAt, hOff⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = w)).1
      have hzero : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = w) := by
          have h' := hy i
          simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at h'
          simp only [idOff, Submodule.mem_iInf]
          intro u
          have := h'.2 ⟨u.1, by rw [u.2]; exact hwv⟩
          exact this
        have h1 : ε * e = e := (hAt e).1 he.1
        have h2 : ε * y i = 0 := (hOff (y i)).1 hyi
        show e * y i = 0
        rw [← h1, mul_comm ε e, mul_assoc, h2, mul_zero]
      rw [hzero]
      exact (latV S L (· = w)).zero_mem

theorem movesLocal : ∀ (D : D7) (S : HSp D) (L : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → ∀ g : GA D S, (GlobalTheory.FinPl.Moves S g L L (fun _ => True) ↔ ∀ v : GlobalTheory.FinPl.Pl D, GlobalTheory.FinPl.Moves S g L L (· = v)) := by
  intro D S L hL g
  have hmv : ∀ (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ i, y i ∈ idAt D P) → ∀ i, (mt S g *ᵥ y) i ∈ idAt D P := by
    intro P y hy i
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  constructor
  · intro h v y hy
    have hyT : ∀ i, y i ∈ idAt D (fun _ => True) := by
      intro i
      have h' := hy i
      simp only [idAt, Submodule.mem_inf] at h' ⊢
      refine ⟨h'.1, ?_⟩
      simp only [Submodule.mem_iInf]
      intro w
      exact absurd trivial w.2
    rw [← movesLocal_supp_iff S L hL.1 v y hy, ← movesLocal_supp_iff S L hL.1 v _ (hmv _ y hy)]
    exact h y hyT
  · intro h y hy
    have hT := fun z => ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (fun _ => True)).2 S).2.2.2 L z hL.1
    rw [hT y, hT (mt S g *ᵥ y)]
    constructor
    · rintro ⟨_, hy'⟩
      refine ⟨hmv _ y hy, fun w _ e he => ?_⟩
      have hey : ∀ i, (e • y) i ∈ idAt D (· = w) := fun i => Ideal.mul_mem_right _ _ he.1
      rw [← Matrix.mulVec_smul]
      exact (h w (e • y) hey).1 (hy' w trivial e he)
    · rintro ⟨_, hy'⟩
      refine ⟨hy, fun w _ e he => ?_⟩
      have hey : ∀ i, (e • y) i ∈ idAt D (· = w) := fun i => Ideal.mul_mem_right _ _ he.1
      refine (h w (e • y) hey).2 ?_
      rw [Matrix.mulVec_smul]
      exact hy' w trivial e he

end GlobalTheory.FinPl
