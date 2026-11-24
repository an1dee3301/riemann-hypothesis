module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Init.ByCases
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Separation.Regular

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx Matrix
open scoped TensorProduct NNReal ENNReal Pointwise Kronecker

namespace GlobalTheory.GaugeEx.ModDet

theorem induction_pi {S : Type} [CommRing S] {ι : Type} [Fintype ι] [DecidableEq ι] {K : ι → Type}
    [∀ k, Field (K k)] (e : S ≃+* ∀ k, K k) {κ : Type} [Fintype κ] [DecidableEq κ]
    (P : Matrix κ κ S → Prop) (hd : ∀ d : κ → S, (∀ i, IsUnit (d i)) → P (diagonal d))
    (ht : ∀ (i j : κ) (c : S), i ≠ j → P (transvection i j c))
    (hm : ∀ A B, P A → P B → P (A * B)) (g : Matrix κ κ S) (hg : IsUnit g.det) : P g := by
  let E : Matrix κ κ S ≃+* ∀ k, Matrix κ κ (K k) := e.mapMatrix.trans Matrix.piRingEquiv
  have hE : ∀ A k i j, E A k i j = e (A i j) k := fun _ _ _ _ => rfl
  have h1 : ∀ k (A : Matrix κ κ (K k)), A.det ≠ 0 → P (E.symm (Pi.mulSingle k A)) := by
    intro k A hA
    apply diagonal_transvection_induction_of_det_ne_zero
      (fun A => P (E.symm (Pi.mulSingle k A))) A hA
    · intro D hD
      rw [det_diagonal] at hD
      have : E.symm (Pi.mulSingle k (diagonal D)) =
          diagonal fun i => e.symm (Pi.mulSingle k (D i)) := by
        rw [RingEquiv.symm_apply_eq]
        funext k'
        ext i j
        rw [hE]
        by_cases hk : k' = k
        · subst hk
          by_cases hij : i = j
          · subst hij; simp
          · simp [hij]
        · by_cases hij : i = j
          · subst hij; simp [hk]
          · simp [hij, hk]
      rw [this]
      refine hd _ fun i => ?_
      have : IsUnit (D i) := (Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)).isUnit
      exact (this.map (MonoidHom.mulSingle K k)).map e.symm
    · intro t
      obtain ⟨a, b, hab, c⟩ := t
      have : E.symm (Pi.mulSingle k (transvection a b c)) =
          transvection a b (e.symm (Pi.single k c)) := by
        rw [RingEquiv.symm_apply_eq]
        funext k'
        ext i j
        rw [hE]
        by_cases hk : k' = k
        · subst hk
          simp [transvection, Matrix.one_apply, Matrix.single, apply_ite e, ite_apply]
        · simp [transvection, Matrix.one_apply, Matrix.single, apply_ite e, ite_apply, hk]
      rw [TransvectionStruct.toMatrix_mk, this]
      exact ht _ _ _ hab
    · intro A B _ _ hA hB
      rw [Pi.mulSingle_mul, map_mul]
      exact hm _ _ hA hB
  have hdet : ∀ k, (E g k).det ≠ 0 := by
    intro k
    have : E g k = ((Pi.evalRingHom K k).comp e.toRingHom).mapMatrix g := rfl
    rw [this, ← RingHom.map_det]
    exact (hg.map _).ne_zero
  have h2 : ∀ s : Finset ι, P (E.symm fun k => if k ∈ s then E g k else 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : (fun k => if k ∈ (∅ : Finset ι) then E g k else 1) = 1 := by funext k; simp
      rw [this, map_one, ← diagonal_one]
      exact hd _ fun _ => isUnit_one
    | insert a s ha ih =>
      have : (fun k => if k ∈ insert a s then E g k else 1) =
          Pi.mulSingle a (E g a) * fun k => if k ∈ s then E g k else 1 := by
        funext k
        by_cases hk : k = a
        · subst hk; simp [ha]
        · simp [hk]
      rw [this, map_mul]
      exact hm _ _ (h1 a _ (hdet a)) ih
  simpa using h2 Finset.univ

section

variable {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [LocallyCompactSpace S]

theorem modu_coe (u : Sˣ) : modu S u = distribHaarChar S u := by
  simp [modu]

theorem modu_mul {a b : S} (ha : IsUnit a) (hb : IsUnit b) : modu S (a * b) = modu S a * modu S b := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  rw [← Units.val_mul, modu_coe, modu_coe, modu_coe, map_mul]


variable [T2Space S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]

theorem smul_map_mulVec_pi [IsArtinianRing S] [IsReduced S] (ν : Measure S) [ν.IsAddHaarMeasure]
    {κ : Type} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ S) (hM : IsUnit M.det) :
    (modu S M.det : ℝ≥0∞) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν) =
      Measure.pi fun _ : κ => ν := by
  classical
  have hm : ∀ A : Matrix κ κ S, Measurable A.mulVec := fun A =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  letI := Fintype.ofFinite (MaximalSpectrum S)
  letI : ∀ m : MaximalSpectrum S, Field (S ⧸ m.asIdeal) := fun m =>
    haveI := m.isMaximal
    Ideal.Quotient.field m.asIdeal
  refine (induction_pi (IsArtinianRing.equivPi S).toRingEquiv (fun M : Matrix κ κ S => IsUnit M.det ∧
    (modu S M.det : ℝ≥0∞) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν) =
      Measure.pi fun _ : κ => ν) ?_ ?_ ?_ M hM).2
  · intro D A
    have hu' : (diagonal D).det = ((∏ i, (A i).unit : Sˣ) : S) := by simp
    refine ⟨hu' ▸ Units.isUnit _, (Measure.pi_eq fun s hs => ?_).symm⟩
    rw [Measure.smul_apply, Measure.map_apply (hm _) (MeasurableSet.univ_pi hs)]
    have : ((diagonal D).mulVec ⁻¹' Set.pi Set.univ fun i : κ => s i) =
        Set.pi Set.univ fun i : κ => ((A i).unit)⁻¹ • s i := by
      ext f
      simp only [Set.mem_preimage, Set.mem_univ_pi, mulVec_diagonal]
      exact forall_congr' fun i => (Set.mem_inv_smul_set_iff (a := (A i).unit)).symm
    rw [this, Measure.pi_pi, hu', modu_coe, map_prod, smul_eq_mul]
    change ENNReal.ofNNRealHom (∏ i, distribHaarChar S (A i).unit) * _ = _
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    change ((distribHaarChar S (A i).unit : ℝ≥0) : ℝ≥0∞) * _ = _
    rw [distribHaarChar_mul, smul_inv_smul]
  · intro a b c hab
    rw [det_transvection_of_ne _ _ hab]
    refine ⟨isUnit_one, ?_⟩
    rw [← Units.val_one, modu_coe, map_one, ENNReal.coe_one, one_smul]
    refine (Measure.pi_eq fun s hs ↦ ?_).symm
    have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
    simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
    rw [lintegral_map (measurable_one.indicator h2s) (hm _)]
    refine lintegral_eq_of_lmarginal_eq {a} ((measurable_one.indicator h2s).comp (hm _))
      (measurable_one.indicator h2s) ?_
    simp_rw [lmarginal_singleton]
    ext x
    simp [transvection, add_mulVec, single_mulVec, hab.symm, ← Function.update_add,
      lintegral_add_right_eq_self fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x a xᵢ)]
  · rintro A B ⟨hA, IHA⟩ ⟨hB, IHB⟩
    have e : (A * B).mulVec = A.mulVec ∘ B.mulVec := funext fun x => (mulVec_mulVec x A B).symm
    rw [det_mul]
    refine ⟨hA.mul hB, ?_⟩
    rw [modu_mul hA hB, ENNReal.coe_mul, mul_smul, e, ← Measure.map_map (hm _) (hm _),
      ← Measure.map_smul, IHB, IHA]
    exact (hm A).aemeasurable

end



end GlobalTheory.GaugeEx.ModDet

end
