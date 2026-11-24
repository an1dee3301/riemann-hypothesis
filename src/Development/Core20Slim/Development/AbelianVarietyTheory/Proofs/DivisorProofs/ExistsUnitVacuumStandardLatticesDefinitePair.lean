module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaAtOfVac
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOver
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Lemmas
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.NeZero
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem DefNode.inRange {X : Node} (h : DefNode D.R.m X) : X.InRange D.R.m := by
  rcases X with ⟨i, j⟩ | i | j
  · exact ⟨h.1, h.2.le⟩
  · exact h.elim
  · exact h

theorem DefNode.sigOK (G : GridData L sc) {X : Node} (h : DefNode D.R.m X) : (G.V X).SigOK := by
  rcases X with ⟨_ | i, j⟩ | i | j
  · obtain rfl := h.2
    have e : G.V (.grid 0 D.R.m) = D.sp.X' := congrArg LSp.sp (colY_m L)
    rw [e]
    exact D.sp.X'_sig
  · exact (G.isV (X := .grid (i + 1) j) ⟨h.1, h.2.le⟩ (by simp)).sigOK
  · exact h.elim
  · exact (G.isV (X := .top j) h (by simp)).sigOK


end GlobalTheory.FunObj

end
