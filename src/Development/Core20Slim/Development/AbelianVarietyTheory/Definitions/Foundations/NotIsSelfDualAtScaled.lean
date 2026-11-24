module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Fin.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.PropLemmas
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

noncomputable section

namespace GlobalTheory.AdelicU.Model

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)








section Supp

omit [NumberField E] in
theorem map_map_tens {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R'']
    [Algebra F R''] (φ : R →ₐ[F] R') (ψ : R' →ₐ[F] R'') (y : R ⊗[F] E) :
    Algebra.TensorProduct.map ψ (AlgHom.id F E) (Algebra.TensorProduct.map φ (AlgHom.id F E) y) =
      Algebra.TensorProduct.map (ψ.comp φ) (AlgHom.id F E) y := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]

omit [NumberField E] in
theorem adTens_eq_one {y : AF F ⊗[F] E} (h1 : ∀ w, compInf F E w y = 1) (h2 : ∀ v, compFin F E v y = 1) : y = 1 := by
  have := GlobalTheory.AutFunCounterexample.tens_inj (F := F) (E := E) (A := Ainf F) (B := Af F) (n := 1) (Matrix.of fun _ _ => y)
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      exact GlobalTheory.AutFunCompare.infTens_ext fun w => (map_map_tens _ _ y).trans ((h1 w).trans (map_one _).symm))
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      exact GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v =>
        (map_map_tens _ _ y).trans ((h2 v).trans (map_one _).symm))
  exact congrFun (congrFun this 0) 0

theorem idem_supp_iff {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (ε : AF F)
    (e0 : ∀ w, evInf F w ε = 0) (e1 : evFin F v ε = 1) (e2 : ∀ u, u ≠ v → evFin F u ε = 0) (g : GAd σ J) :
    (∀ i j, algebraMap (AF F) (AF F ⊗[F] E) ε * ((matHom _ σ J g).1 - 1) i j = ((matHom _ σ J g).1 - 1) i j) ↔
      g ∈ (emb σ J v).range := by
  have c0 : ∀ w, compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) ε) = 0 := fun w => by
    change evInf F w ε ⊗ₜ[F] (1 : E) = 0
    rw [e0, TensorProduct.zero_tmul]
  have c1 : compFin F E v (algebraMap (AF F) (AF F ⊗[F] E) ε) = 1 := by
    change evFin F v ε ⊗ₜ[F] (1 : E) = 1
    rw [e1]; rfl
  have c2 : ∀ u, u ≠ v → compFin F E u (algebraMap (AF F) (AF F ⊗[F] E) ε) = 0 := fun u hu => by
    change evFin F u ε ⊗ₜ[F] (1 : E) = 0
    rw [e2 u hu, TensorProduct.zero_tmul]
  have one : ∀ {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (m : Matrix (Fin n) (Fin n) A),
      m.map φ = 1 ↔ ∀ i j, φ ((m - 1) i j) = 0 := fun φ m => by
    rw [← Matrix.ext_iff]
    refine forall₂_congr fun i j => ?_
    rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have pf : ∀ u, proj σ J u g = 1 ↔ ∀ i j, compFin F E u (((matHom _ σ J g).1 - 1) i j) = 0 := fun u =>
    Iff.trans ⟨fun h => congrArg (fun x => (matHom _ σ J x).1) h, fun h => Subtype.ext (Units.ext h)⟩ (one _ _)
  have pa : ∀ w, projArch σ J w g = 1 ↔ ∀ i j, compInf F E w (((matHom _ σ J g).1 - 1) i j) = 0 := fun u =>
    Iff.trans ⟨fun h => congrArg (fun x => (matHom _ σ J x).1) h, fun h => Subtype.ext (Units.ext h)⟩ (one _ _)
  rw [range_emb, mem_atPts, mem_finPts_iff_forall]
  simp only [pf, pa, Finset.mem_singleton]
  constructor
  · intro h
    exact ⟨fun w i j => by rw [← h, map_mul, c0, zero_mul], fun u hu i j => by rw [← h, map_mul, c2 u hu, zero_mul]⟩
  · rintro ⟨h1, h2⟩ i j
    rw [← sub_eq_zero, ← add_eq_right (b := 1)]
    refine adTens_eq_one (fun w => ?_) fun u => ?_
    · rw [map_add (f := _), map_sub, map_mul, h1, map_one]; simp
    · rw [map_add (f := _), map_sub, map_mul, map_one]
      by_cases hu : u = v
      · subst hu; rw [c1]; simp
      · rw [h2 u hu]; simp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem suppF_iff {D : D7} (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (h : IsPlaceIdem D v ε) (g : GA D V) :
    Formalism.IndefR.Mult.SuppF V (algebraMap (AF D.host.F) (AE D) ε) g ↔ g ∈ (emb D.sp.cm.sig V.gram v).range := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  exact idem_supp_iff _ _ v _ (fun _ => rfl) h1 h2 g


end Supp

section More

end More

end GlobalTheory.AdelicU.Model
