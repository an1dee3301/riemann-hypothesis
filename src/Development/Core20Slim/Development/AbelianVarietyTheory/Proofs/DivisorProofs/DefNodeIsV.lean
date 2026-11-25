module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFirstColumnSpaceRankSignatureSelfDual
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Prelude
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj

theorem defNode_isV {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (μ0 : T) (hL : L.Is μ0)
    (X : Node) (hX : DefNode D.R.m X) : (G.node X).IsV (X.rank D) 0 := by
  rcases X with ⟨i, j⟩ | i | j
  · obtain ⟨hi, rfl⟩ := hX
    rcases i with _ | i
    · have h := colY_isV D T L μ0 hL D.R.m le_rfl
      rw [Nat.sub_self, Nat.zero_div] at h
      exact h
    · have h := G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (fun j h => by cases h)
      simp only [Node.neg, Nat.sub_self, Nat.zero_div] at h
      exact h
  · exact absurd hX id
  · exact G.isV (X := .top j) hX (fun j' h => by cases h)





end GlobalTheory.FunObj
