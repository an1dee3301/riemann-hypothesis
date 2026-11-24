module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinTensAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Formalism.RankGapBounds.MeanBoundSecondForm
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Filter.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Neighborhoods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict 
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.SplitClass

open GlobalTheory.SplitScalar

section Adelic

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem exists_rat_sub_mem {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {Λ : AddSubgroup (WO S T)}
    (hΛ : ∃ U : Set (WO S T), IsOpen U ∧ ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ u ∈ U))
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    ∃ γ, (LatVac.finTens 1 γ : WO S T) ∈ (latO S T LS LT fun _ => True) ∧ u - LatVac.finTens 1 γ ∈ Λ := by
  obtain ⟨U, hU, hUΛ⟩ := hΛ
  have hfin : ∀ (α : Af D.host.F) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E),
      (LatVac.finTens α M : WO S T).map (infPart D) = 0 := fun α M =>
    Matrix.ext fun i j => LatVac.infPart_pair _ _
  refine LatVac.latO_induction (p := fun u => ∃ γ,
    (LatVac.finTens 1 γ : WO S T) ∈ (latO S T LS LT fun _ => True) ∧ u - LatVac.finTens 1 γ ∈ Λ) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    let φ : Af D.host.F →+ WO S T := AddMonoidHom.mk' (fun β => LatVac.finTens β M)
      fun a b => LatVac.finTens_add_left a b M
    let C : AddSubgroup (Af D.host.F) :=
      { carrier := {β | ∃ γ, (LatVac.finTens 1 γ : WO S T) ∈ (latO S T LS LT fun _ => True) ∧
          φ β - LatVac.finTens 1 γ ∈ Λ}
        zero_mem' := ⟨0, by rw [LatVac.finTens_zero]; exact zero_mem _,
          by rw [LatVac.finTens_zero, map_zero, sub_self]; exact zero_mem _⟩
        add_mem' := by
          rintro a b ⟨γ, h1, h2⟩ ⟨γ', h1', h2'⟩
          refine ⟨γ + γ', by rw [LatVac.finTens_add]; exact add_mem h1 h1', ?_⟩
          rw [LatVac.finTens_add, map_add (f := _), add_sub_add_comm]
          exact add_mem h2 h2'
        neg_mem' := by
          rintro a ⟨γ, h1, h2⟩
          refine ⟨-γ, by rw [LatVac.finTens_neg]; exact neg_mem h1, ?_⟩
          rw [LatVac.finTens_neg, map_neg, neg_sub_neg, ← neg_sub]
          exact neg_mem h2 }
    have hc := VacSign.continuous_finTens (D := D) M
    have hop : IsOpen (C : Set (Af D.host.F)) := by
      refine C.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset
        ((hU.preimage hc).mem_nhds ?_) fun β hβ => ⟨0, ?_, ?_⟩)
      · refine (hUΛ _ (hfin _ _)).1 ?_
        rw [LatVac.finTens_zero_left]
        exact zero_mem _
      · rw [LatVac.finTens_zero]; exact zero_mem _
      · rw [LatVac.finTens_zero, sub_zero]
        exact (hUΛ _ (hfin _ _)).2 hβ
    refine IntDense.mem_of_isClosed D.host.F (C := (C : Set (Af D.host.F))) (C.isClosed_of_isOpen hop)
      (fun a => ?_) α hα
    have hm : LatVac.finTens (algebraMap D.host.F (Af D.host.F) (a : D.host.F)) M ∈
        latO S T LS LT fun _ => True :=
      LatVac.finTens_mem_latO (fun v => by
        rw [AlgHom.commutes]; exact v.coe_algebraMap_mem (𝓞 D.host.F) D.host.F a) hM
    rw [VacSign.finTens_algebraMap] at hm
    refine ⟨_, hm, ?_⟩
    rw [← VacSign.finTens_algebraMap]
    change LatVac.finTens _ M - LatVac.finTens _ M ∈ Λ
    rw [sub_self]
    exact zero_mem _
  · exact ⟨0, by rw [LatVac.finTens_zero]; exact zero_mem _,
      by rw [LatVac.finTens_zero, sub_self]; exact zero_mem _⟩
  · rintro a b ⟨γ, h1, h2⟩ ⟨γ', h1', h2'⟩
    refine ⟨γ + γ', by rw [LatVac.finTens_add]; exact add_mem h1 h1', ?_⟩
    rw [LatVac.finTens_add, add_sub_add_comm]
    exact add_mem h2 h2'
  · rintro a ⟨γ, h1, h2⟩
    refine ⟨-γ, by rw [LatVac.finTens_neg]; exact neg_mem h1, ?_⟩
    rw [LatVac.finTens_neg, neg_sub_neg, ← neg_sub]
    exact neg_mem h2

theorem exists_reps {G ι : Type} [AddCommGroup G] (Λ : AddSubgroup G) (P : G → Prop) (s : Finset ι) (a : ι → G)
    (h : ∀ u, P u → ∃ i ∈ s, u - a i ∈ Λ) :
    ∃ R : Finset G, (∀ u ∈ R, P u) ∧ ∀ u, P u → ∃! v, v ∈ R ∧ u - v ∈ Λ := by
  have hfin : (QuotientAddGroup.mk '' {u | P u} : Set (G ⧸ Λ)).Finite := by
    refine ((s.finite_toSet).image fun i => (QuotientAddGroup.mk (a i) : G ⧸ Λ)).subset ?_
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨i, hi, h⟩ := h u hu
    exact ⟨i, hi, (QuotientAddGroup.eq_iff_sub_mem.2 h).symm⟩
  obtain ⟨t, ht, hb⟩ := Set.exists_subset_bijOn {u | P u} (QuotientAddGroup.mk : G → G ⧸ Λ)
  have htf : t.Finite := Set.Finite.of_finite_image (hb.image_eq ▸ hfin) hb.injOn
  refine ⟨htf.toFinset, fun u hu => ht (htf.mem_toFinset.1 hu), fun u hu => ?_⟩
  obtain ⟨v, hv, h⟩ := hb.surjOn ⟨u, hu, rfl⟩
  refine ⟨v, ⟨htf.mem_toFinset.2 hv, QuotientAddGroup.eq_iff_sub_mem.1 h.symm⟩, fun v' hv' => ?_⟩
  exact hb.injOn (htf.mem_toFinset.1 hv'.1) hv ((QuotientAddGroup.eq_iff_sub_mem.2 hv'.2).symm.trans h.symm)



end Adelic

section Reading

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {r g : ℕ} {hr : W.rank = r}
  {X : Data D.host.E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {x : Frame X.Ψ r}




theorem finTens_sub {m n : ℕ} (M N : Matrix (Fin m) (Fin n) D.host.E) :
    LatVac.finTens (D := D) 1 (M - N) = LatVac.finTens 1 M - LatVac.finTens 1 N := by
  rw [sub_eq_add_neg, LatVac.finTens_add, LatVac.finTens_neg, sub_eq_add_neg]





end Reading



end GlobalTheory.AdTh.SplitClass

end
