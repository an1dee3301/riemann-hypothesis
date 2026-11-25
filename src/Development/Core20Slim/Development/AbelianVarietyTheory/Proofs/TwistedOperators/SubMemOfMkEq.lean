module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Quot
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

section Quot

variable {V : Type} [AddCommGroup V]

abbrev mLat (m : ℕ) (Λ : AddSubgroup V) : AddSubgroup V := Λ.map (nsmulAddMonoidHom m)

abbrev Qm (m : ℕ) (Λ : AddSubgroup V) : Type := Λ ⧸ (mLat m Λ).addSubgroupOf Λ

def repm {m : ℕ} {Λ : AddSubgroup V} (q : Qm m Λ) : V := ((Quotient.out q : Λ) : V)

theorem mem_mLat {m : ℕ} {Λ : AddSubgroup V} {x : V} : x ∈ mLat m Λ ↔ ∃ l ∈ Λ, m • l = x := by
  simp [mLat]

theorem repm_mem {m : ℕ} {Λ : AddSubgroup V} (q : Qm m Λ) : repm q ∈ Λ := (Quotient.out q : Λ).2

theorem mk_repm {m : ℕ} {Λ : AddSubgroup V} (q : Qm m Λ) :
    (QuotientAddGroup.mk (⟨repm q, repm_mem q⟩ : Λ) : Qm m Λ) = q := by
  have : (⟨repm q, repm_mem q⟩ : Λ) = Quotient.out q := rfl
  rw [this]
  exact QuotientAddGroup.out_eq' q

theorem sub_mem_of_mk_eq {m : ℕ} {Λ : AddSubgroup V} {a b : V} (ha : a ∈ Λ) (hb : b ∈ Λ)
    (h : (QuotientAddGroup.mk (⟨a, ha⟩ : Λ) : Qm m Λ) = QuotientAddGroup.mk (⟨b, hb⟩ : Λ)) : b - a ∈ mLat m Λ := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
  simpa [sub_eq_neg_add] using h

theorem repm_mk_sub {m : ℕ} {Λ : AddSubgroup V} {a : V} (ha : a ∈ Λ) :
    repm (QuotientAddGroup.mk (⟨a, ha⟩ : Λ) : Qm m Λ) - a ∈ mLat m Λ :=
  sub_mem_of_mk_eq (m := m) ha (repm_mem _) (mk_repm _).symm

theorem repm_add_sub {m : ℕ} {Λ : AddSubgroup V} (q q' : Qm m Λ) :
    repm (q + q') - (repm q + repm q') ∈ mLat m Λ := by
  refine sub_mem_of_mk_eq (m := m) (Λ.add_mem (repm_mem q) (repm_mem q')) (repm_mem (q + q')) ?_
  rw [mk_repm]
  conv_rhs => rw [← mk_repm q, ← mk_repm q']
  rfl

theorem repm_zero_mem {m : ℕ} {Λ : AddSubgroup V} : repm (0 : Qm m Λ) ∈ mLat m Λ := by
  have h := repm_mk_sub (m := m) (Λ := Λ) Λ.zero_mem
  have h0 : (QuotientAddGroup.mk (⟨0, Λ.zero_mem⟩ : Λ) : Qm m Λ) = 0 := rfl
  rw [h0, sub_zero] at h
  exact h

end Quot

variable {D : D7}

def lamE (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (x : WO S T) : ℂ :=
  ψ (symplOH S T (e • x) (cA D e • x))

end GlobalTheory.FinDecomp

end
