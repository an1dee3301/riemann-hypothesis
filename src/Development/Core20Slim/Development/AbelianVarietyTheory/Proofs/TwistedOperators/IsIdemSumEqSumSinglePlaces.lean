module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSumPartialProperties
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.ByCases
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.IdemSingleSum

theorem sum_mul_sum_orth {R ι : Type} [Ring R] [DecidableEq ι] (f : ι → R) (hid : ∀ i, f i * f i = f i)
    (horth : ∀ i j, i ≠ j → f i * f j = 0) (S S' : Finset ι) :
    (∑ i ∈ S, f i) * (∑ j ∈ S', f j) = ∑ i ∈ S ∩ S', f i := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  calc ∑ i ∈ S, ∑ j ∈ S', f i * f j = ∑ i ∈ S, if i ∈ S' then f i else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : i ∈ S'
        · rw [if_pos hi, Finset.sum_eq_single_of_mem i hi fun j _ hji => horth i j (Ne.symm hji), hid]
        · rw [if_neg hi]
          exact Finset.sum_eq_zero fun j hj => horth i j fun hij => hi (by rw [hij]; exact hj)
    _ = ∑ i ∈ S ∩ S', f i := Finset.sum_ite_mem S S' f

theorem isIdemAt_of_single {D : D7} {a : AE D} {w : Pl D.host.E} (h : IsIdemSum a {w}) :
    Formalism.L2.NTheta.IsIdemAt a w := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  simpa using hes w (Finset.mem_singleton_self w)

private theorem mul_self_eq_of_isIdemAt {D : D7} {x : AE D} {w : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x w) : x * x = x := by
  have h := GlobalTheory.PartialIdemSum.mul_sum_of_isIdemAt hx {w} (fun _ => x) (by simpa using hx)
  simpa only [Finset.sum_singleton, Finset.mem_singleton_self, if_true] using h

private theorem mul_eq_zero_of_isIdemAt_of_ne {D : D7} {x y : AE D} {w w' : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x w) (hy : Formalism.L2.NTheta.IsIdemAt y w') (hne : w ≠ w') : x * y = 0 := by
  have h := GlobalTheory.PartialIdemSum.mul_sum_of_isIdemAt hx {w'} (fun _ => y) (by simpa using hy)
  rwa [Finset.sum_singleton, if_neg (by simpa using hne)] at h

private theorem eq_of_isIdemAt_of_isIdemAt {D : D7} {x y : AE D} {w : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x w) (hy : Formalism.L2.NTheta.IsIdemAt y w) : x = y := by
  have h1 := GlobalTheory.PartialIdemSum.mul_sum_of_isIdemAt hx {w} (fun _ => y) (by simpa using hy)
  have h2 := GlobalTheory.PartialIdemSum.mul_sum_of_isIdemAt hy {w} (fun _ => x) (by simpa using hx)
  simp only [Finset.sum_singleton, Finset.mem_singleton_self, if_true] at h1 h2
  calc x = x * y := h1.symm
    _ = y * x := mul_comm x y
    _ = y := h2

theorem sum_single : ∀ (D : D7) (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ (eL : P → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → e = ∑ w, eL w ∧ (∀ S : Finset P, IsIdemSum (∑ w ∈ S, eL w) (S.map (Function.Embedding.subtype _))) ∧ ∀ S S' : Finset P, (∑ w ∈ S, eL w) * (∑ w ∈ S', eL w) = ∑ w ∈ S ∩ S', eL w := by
  intro D e P he eL hL
  obtain ⟨⟨es, hes, hsum⟩, he0⟩ := he
  have hat : ∀ w : P, Formalism.L2.NTheta.IsIdemAt (eL w) w.1 := fun w => isIdemAt_of_single (hL w)
  have hprod : ∀ S S' : Finset P, (∑ w ∈ S, eL w) * (∑ w ∈ S', eL w) = ∑ w ∈ S ∩ S', eL w := fun S S' =>
    sum_mul_sum_orth eL (fun w => mul_self_eq_of_isIdemAt (hat w))
      (fun w w' hne => mul_eq_zero_of_isIdemAt_of_ne (hat w) (hat w') fun h => hne (Subtype.ext h)) S S'
  have htot : e = ∑ w, eL w := by
    rw [hsum, ← Finset.sum_coe_sort P es]
    exact Finset.sum_congr rfl fun w _ => (eq_of_isIdemAt_of_isIdemAt (hat w) (hes w.1 w.2)).symm
  refine ⟨htot, fun S => ⟨⟨es, ?_, ?_⟩, ?_⟩, hprod⟩
  · intro PP hPP
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hPP
    exact hes w.1 w.2
  · rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun w _ => eq_of_isIdemAt_of_isIdemAt (hat w) (hes w.1 w.2)
  · have hse : (∑ w ∈ S, eL w) * e = ∑ w ∈ S, eL w := by
      rw [htot, hprod, Finset.inter_univ]
    set s := ∑ w ∈ S, eL w
    calc s * cA D s = (s * e) * cA D (e * s) := by rw [hse, mul_comm e s, hse]
      _ = s * (e * cA D e) * cA D s := by rw [map_mul]; ring
      _ = 0 := by rw [he0, mul_zero, zero_mul]

end GlobalTheory.IdemSingleSum
