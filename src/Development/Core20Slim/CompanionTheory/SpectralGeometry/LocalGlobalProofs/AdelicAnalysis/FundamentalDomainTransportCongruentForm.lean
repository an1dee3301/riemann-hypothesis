module

public import Mathlib
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import Development.Core20Slim.CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryIsomOfIsometry
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Real

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FTransfer

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem actTup_ratTup {M n : ℕ} (g : GL (Fin M) E) (X : Fin n → Fin M → E) :
    actTup R (bc (inclR (F := F) R) g) (ratTup R X) =
      ratTup R (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) := by
  funext a i
  have h := RingHom.map_mulVec (inclR (F := F) R) (g : Matrix (Fin M) (Fin M) E) (X a) i
  exact h.symm

theorem actTup_mul {M n : ℕ} (a b : GL (Fin M) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) :
    actTup R (a * b) X = actTup R a (actTup R b X) := by
  funext c
  simp [actTup, Matrix.mulVec_mulVec]

end Alg

section Group

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R]

theorem isTopologicalGroup_HA [IsTopologicalRing R] [Module.Finite F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : IsTopologicalGroup (HA R σ J) := by
  haveI : IsTopologicalRing (R ⊗[F] E) := GlobalTheory.CompanionTheory.SW.HIsom.isTopologicalRing_tens F E R
  exact inferInstanceAs (IsTopologicalGroup (HR R σ J))

theorem borelSpace_HA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    BorelSpace (HA R σ J) := ⟨rfl⟩

end Group

end GlobalTheory.CompanionTheory.SW.FTransfer


open GlobalTheory.CompanionTheory.SW.FTransfer in
theorem GlobalTheory.CompanionTheory.SW.FTransfer.cntI_transfer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : GL (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), J' = cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∃ (μ' : Measure (HA (AF F) σ J')) (𝓕' : Set (HA (AF F) σ J')), IsHaarH F E σ M J' μ' ∧ IsFDH F E σ M J' μ' 𝓕' ∧ μ' 𝓕' = μ 𝓕 ∧ ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞), cntI σ J μ 𝓕 S Φ = cntI σ J' μ' 𝓕' {X | (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) ∈ S} (fun Y => Φ (actTup (AF F) (bc (inclR (AF F)) g) Y)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ g J' hJ' μ 𝓕 hμ h𝓕
  obtain ⟨e, he1, he2⟩ := GlobalTheory.CompanionTheory.SW.HIsom.unitaryIsom_of_isometry F E σ hCM M J hJ g J' hJ' (AF F)
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  haveI := isTopologicalGroup_HA (F := F) (E := E) (AF F) σ J
  haveI := isTopologicalGroup_HA (F := F) (E := E) (AF F) σ J'
  haveI := borelSpace_HA (F := F) (E := E) (AF F) σ J
  haveI := borelSpace_HA (F := F) (E := E) (AF F) σ J'
  haveI : μ.IsHaarMeasure := hμ
  let em : HA (AF F) σ J' ≃ᵐ HA (AF F) σ J := e.toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving em (μ.map em.symm) μ := by
    refine ⟨em.measurable, ?_⟩
    rw [Measure.map_map em.measurable em.symm.measurable]
    simp
  refine ⟨μ.map em.symm, em ⁻¹' 𝓕, ?_, ?_, ?_, ?_⟩
  · exact ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  · have hq : Measure.QuasiMeasurePreserving em (μ.map em.symm) μ := hmp.quasiMeasurePreserving
    have hin₀ : ∀ x : HA (AF F) σ J, HA.mat (AF F) σ J x ∈ HFin (AF F) σ J →
        HA.mat (AF F) σ J' (e.symm x) ∈ HFin (AF F) σ J' := by
      intro x hx
      apply (he2 _).1
      rw [e.apply_symm_apply]
      exact hx
    have hin : ∀ a : HFinIn (AF F) σ J,
        HA.mat (AF F) σ J' (e.symm (a.1 : HA (AF F) σ J)) ∈ HFin (AF F) σ J' :=
      fun a => hin₀ a.1 a.2
    have hmulx : ∀ (y : HA (AF F) σ J) (x : HA (AF F) σ J'), e (e.symm y * x) = y * e x := by
      intro y x
      rw [map_mul, e.apply_symm_apply]
    let e' : HFinIn (AF F) σ J → HFinIn (AF F) σ J' := fun a =>
      ⟨(e.symm (a.1 : HA (AF F) σ J) : HA (AF F) σ J'), Subgroup.mem_subgroupOf.2 (hin a)⟩
    refine IsFundamentalDomain.preimage_of_equiv h𝓕 hq (e := e') ⟨?_, ?_⟩ ?_
    · intro a b hab
      have h1 : e.symm (a.1 : HA (AF F) σ J) = e.symm (b.1 : HA (AF F) σ J) :=
        congrArg (fun x : HFinIn (AF F) σ J' => (x.1 : HA (AF F) σ J')) hab
      exact Subtype.ext (e.symm.injective h1)
    · intro b
      have hb : HA.mat (AF F) σ J (e (b.1 : HA (AF F) σ J')) ∈ HFin (AF F) σ J :=
        (he2 _).2 b.2
      refine ⟨⟨(e (b.1 : HA (AF F) σ J') : HA (AF F) σ J), Subgroup.mem_subgroupOf.2 hb⟩, ?_⟩
      exact Subtype.ext (e.symm_apply_apply (b.1 : HA (AF F) σ J'))
    · intro a x
      exact hmulx a.1 x
  · rw [em.symm.map_apply]
    congr 1
    ext x
    simp
  · intro n S Φ
    have hrest : (μ.map em.symm).restrict (em ⁻¹' 𝓕) = (μ.restrict 𝓕).map em.symm := by
      rw [MeasurableEquiv.restrict_map]
      congr 2
      ext x
      simp
    unfold cntI
    rw [hrest, lintegral_map_equiv]
    refine lintegral_congr fun h => ?_
    have key : ∀ X : Fin n → Fin M → E,
        actTup (AF F) (bc (inclR (AF F)) g)
            (actW (AF F) σ J' (em.symm h)⁻¹ (ratTup (AF F) X)) =
          actW (AF F) σ J h⁻¹
            (ratTup (AF F) (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a)) := by
      intro X
      have hu : e (em.symm h) = h := e.apply_symm_apply h
      have h1 := he1 (em.symm h)⁻¹
      rw [map_inv, hu] at h1
      simp only [actW]
      rw [← actTup_ratTup, h1, ← actTup_mul, ← actTup_mul]
      congr 1
      group
    let T : {X : Fin n → Fin M → E | (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) ∈ S} ≃ S :=
      { toFun := fun X => ⟨fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X.1 a, X.2⟩
        invFun := fun Y => ⟨fun a => ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ Y.1 a, by
          have : (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ
              (((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ Y.1 a)) = Y.1 := by
            funext a
            rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
              Matrix.one_mulVec]
          change (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ
              (((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ Y.1 a)) ∈ S
          rw [this]
          exact Y.2⟩
        left_inv := fun X => by
          apply Subtype.ext
          funext a
          change ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ
            ((g : Matrix (Fin M) (Fin M) E) *ᵥ X.1 a) = X.1 a
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mulVec]
        right_inv := fun Y => by
          apply Subtype.ext
          funext a
          change (g : Matrix (Fin M) (Fin M) E) *ᵥ
            (((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ Y.1 a) = Y.1 a
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.one_mulVec] }
    refine (T.tsum_eq (fun X : S => Φ (actW (AF F) σ J h⁻¹
      (ratTup (AF F) (X : Fin n → Fin M → E))))).symm.trans (tsum_congr fun X => ?_)
    exact congrArg Φ (key X.1).symm
