module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitPlaceEmb

theorem not_isField_of_idem {A : Type} [CommRing A] (σ : A →+* A) {z : A} (hz : z * z = z) (h : z + σ z = 1) :
    ¬ IsField A := by
  intro hf
  haveI := hf.isDomain
  have h0 : z * (z - 1) = 0 := by rw [mul_sub, hz, mul_one, sub_self]
  rcases mul_eq_zero.1 h0 with h' | h'
  · rw [h', σ.map_zero, zero_add] at h
    exact zero_ne_one h
  · rw [sub_eq_zero.1 h', σ.map_one] at h
    exact one_ne_zero (add_eq_left.1 h)

theorem nonempty_algHom_of_idem {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]
    (hE : Module.finrank F E = 2) (σ : E →ₐ[F] E) {z : K ⊗[F] E} (hz : z * z = z)
    (h : z + (Algebra.TensorProduct.map (AlgHom.id F K) σ).toRingHom z = 1) : Nonempty (E →ₐ[F] K) := by
  have h2 : Module.finrank K (K ⊗[F] E) = 2 := by rw [Module.finrank_baseChange, hE]
  obtain ⟨φ⟩ := GlobalTheory.AdelicU.nonempty_algHom_of_not_isField (K := K) h2
    (not_isField_of_idem (Algebra.TensorProduct.map (AlgHom.id F K) σ).toRingHom hz h)
  exact ⟨(φ.restrictScalars F).comp Algebra.TensorProduct.includeRight⟩

theorem nonempty_algHom_of_idem_map {F E K R : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]
    [CommRing R] [Algebra F R] (hE : Module.finrank F E = 2) (σ : E →ₐ[F] E) (ψ : R →ₐ[F] K) {e : R ⊗[F] E}
    {ε : R} (he : e * e = e) (hs : e + (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom e = algebraMap R _ ε)
    (hψ : ψ ε = 1) : Nonempty (E →ₐ[F] K) := by
  let Φ : R ⊗[F] E →+* K ⊗[F] E := (Algebra.TensorProduct.map ψ (AlgHom.id F E)).toRingHom
  let τ : K ⊗[F] E →+* K ⊗[F] E := (Algebra.TensorProduct.map (AlgHom.id F K) σ).toRingHom
  have hcomm : ∀ x, Φ ((Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom x) = τ (Φ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  refine nonempty_algHom_of_idem hE σ (z := Φ e) (by rw [← map_mul, he]) ?_
  have := congrArg Φ hs
  rw [map_add (f := _), hcomm] at this
  rw [this, Algebra.TensorProduct.algebraMap_apply]
  change ψ ε ⊗ₜ[F] (1 : E) = 1
  rw [hψ]
  rfl

theorem nonempty_algHom_of_not_nonSplitAt :
    ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    ¬ GlobalTheory.WeilParts.NonSplitAt D v ε → Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v) := by
  intro D v ε hε hn
  obtain ⟨e, ⟨he, -, -⟩, hsum⟩ : ∃ e : AE D, IsSplitIdem D e ∧ e + cA D e = algebraMap _ _ ε := by
    by_contra h
    exact hn ⟨hε, h⟩
  obtain ⟨α, rfl, h1, -⟩ := hε
  exact nonempty_algHom_of_idem_map (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 D.sp.cm.sig
    ((evalV D.host.F v).comp (sndA D.host.F)) he hsum h1

end GlobalTheory.SplitPlaceEmb

end
