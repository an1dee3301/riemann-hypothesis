module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

namespace GlobalTheory.RowClaim.TermVolDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

theorem isDefiniteSpace_of_isV {X : LSp D} {ν : ℕ} (h : X.IsV ν 0) : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace X.sp :=
  ⟨h.sigOK, fun τ => Or.inl (by rw [h.sig τ, h.rank, Nat.sub_zero])⟩

theorem isMeasDef_of_isTermVol {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U)
    {μ₀ : T} (hL : L.Is μ₀) (t : T) (Φ : G.Datum) (β : CosFam G t) (M : Vol G) (hM : IsTermVol t S Φ β M) :
    (∀ j (h : j < D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace (G.V (.top j)) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel (G.V (.top j)) (S.levTop t Φ β j h) ∧
      IsMeasDef (G.V (.top j)) (S.levTop t Φ β j h) (M.ν (.top j)) (M.fd (.top j))) ∧
    ∀ i (h : i ≤ D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace (G.V (.grid i D.R.m)) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel (G.V (.grid i D.R.m)) (S.levRow t i h) ∧
      IsMeasDef (G.V (.grid i D.R.m)) (S.levRow t i h) (M.ν (.grid i D.R.m)) (M.fd (.grid i D.R.m)) := by
  refine ⟨fun j h => ⟨?_, S.isCO_levTop W t Φ β h, ?_⟩, fun i h => ⟨?_, S.isCO_levRow W t h, ?_⟩⟩
  · exact isDefiniteSpace_of_isV (node_isV G hL (X := .top j) h.le)
  · have e := hM.1 j h
    unfold Vol.IsAt at e
    rw [if_pos (by simp [Node.neg])] at e
    exact e
  · have hV := node_isV G hL (X := .grid i D.R.m) ⟨h, le_rfl⟩
    have e : Node.neg D.R.m (.grid i D.R.m) = 0 := by simp [Node.neg]
    rw [e] at hV
    exact isDefiniteSpace_of_isV hV
  · have e := hM.2 i h
    unfold Vol.IsAt at e
    rw [if_pos (by simp [Node.neg])] at e
    exact e

end GlobalTheory.RowClaim.TermVolDef

end
