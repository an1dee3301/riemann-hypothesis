module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Init.SizeOf
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) (x : R ⊗[F] E) :
    sigR R' σ (Algebra.TensorProduct.map f (AlgHom.id F E) x) =
      Algebra.TensorProduct.map f (AlgHom.id F E) (sigR R σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def hermMap {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {n : ℕ} (S : HermR R σ n) : HermR R' σ n :=
  ⟨(S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map (Algebra.TensorProduct.map f (AlgHom.id F E)), by
    intro a b
    have h : sigR R σ ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) b a) = (S : Matrix _ _ _) a b := S.2 a b
    simp only [Matrix.map_apply]
    rw [sigR_map, h]⟩

theorem hermMap_sub {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {n : ℕ} (S T : HermR R σ n) :
    hermMap f σ (S - T) = hermMap f σ S - hermMap f σ T := by
  apply Subtype.ext
  funext a b
  simp [hermMap]

theorem hermMap_hermOf {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) :
    hermMap f σ (HeckeCharacterZeroLocus.SiegelWeilU.hermOf R σ T hT) = HeckeCharacterZeroLocus.SiegelWeilU.hermOf R' σ T hT := by
  apply Subtype.ext
  funext a b
  simp [hermMap, HeckeCharacterZeroLocus.SiegelWeilU.hermOf, HeckeCharacterZeroLocus.SiegelWeilU.inclR]

theorem sigR_hR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J y x) = hR R σ J x y := by
  have h2 : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR, hσ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h3 : ∀ i j, sigR R σ (JR R J i j) = JR R J j i := by
    intro i j
    simp [sigR, JR, inclR, hJ j i]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, map_sum, map_mul, h2, h3]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hermMap_hR {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (hR R σ J x y) =
      hR R' σ J (fun i => Algebra.TensorProduct.map f (AlgHom.id F E) (x i))
        (fun i => Algebra.TensorProduct.map f (AlgHom.id F E) (y i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, map_sum, map_mul, sigR_map]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [JR, inclR]

end Alg

section Cm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_invol {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ]
  simp

def gramH {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : HermR R σ n :=
  ⟨gramR R σ J X, fun a c => sigR_hR R σ (sig_invol hCM) hJ.1 (X a) (X c)⟩

theorem hermMap_gramH {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    hermMap f σ (gramH hCM hJ R X) =
      gramH hCM hJ R' (fun a i => Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)) := by
  apply Subtype.ext
  funext a c
  exact hermMap_hR f σ J (X a) (X c)

end Cm

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def boxFN {M n : ℕ} (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)) :
    Set (Fin n → Fin M → Af F ⊗[F] E) :=
  {X | ∀ v, projV v X ∈ A v}

def pureN {M n : ℕ} (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (X : Fin n → Fin M → AF F ⊗[F] E) : ℂ :=
  φ (projInf X) * (boxFN A).indicator (fun _ => (1 : ℂ)) (projFin X)

def hermInf (σ : E →ₐ[F] E) {n : ℕ} (S : HermR (AF F) σ n) : HermR (Ainf F) σ n := hermMap (fstA F) σ S

def hermFin (σ : E →ₐ[F] E) {n : ℕ} (S : HermR (AF F) σ n) : HermR (Af F) σ n := hermMap (sndA F) σ S

def hermV (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (S : HermR (Af F) σ n) : HermR (Fv F v) σ n :=
  hermMap (evalV F v) σ S

def latH {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    Set (HermR (Fv F v) σ n) :=
  {S | (∀ i, algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
        ((S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i i) ∈ v.adicCompletionIntegers F) ∧
    ∀ i j, i < j → ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr
      ((S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i j) k ∈ v.adicCompletionIntegers F}

def intH {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Set (HermR (Af F) σ n) :=
  {y | ∀ v, v ∉ S → hermV σ v y ∈ latH σ b v n}

def boxH {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n)) : Set (HermR (Af F) σ n) :=
  {y | (∀ v ∈ S, hermV σ v y ∈ U v) ∧ ∀ v, v ∉ S → hermV σ v y ∈ latH σ b v n}

def testH {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) {n : ℕ} (ρ : HermR (Ainf F) σ n → ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n))
    (y : HermR (AF F) σ n) : ℂ :=
  (ρ (hermInf σ y) : ℂ) * (boxH σ b n S U).indicator (fun _ => (1 : ℂ)) (hermFin σ y)

def fouH (σ : E →ₐ[F] E) {n : ℕ} (ψ : AddChar (AF F) ℂ) (db : Measure (HermR (AF F) σ n))
    (τ : HermR (AF F) σ n → ℂ) (b : HermR (AF F) σ n) : ℂ :=
  ∫ y, τ y * ψ (pairHerm (AF F) σ n y b) ∂db

def chiT (σ : E →ₐ[F] E) {n : ℕ} (ψ : AddChar (AF F) ℂ) (T : Matrix (Fin n) (Fin n) E)
    (y : HermR (AF F) σ n) : ℂ :=
  ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
    (Matrix.trace (T.map (inclR (AF F)) * (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))))))

def coefSN {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (ψ : AddChar (AF F) ℂ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (T : Matrix (Fin n) (Fin n) E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ℂ :=
  ∫ y, (intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y) *
    (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * chiT σ ψ T y) ∂db

end Adelic

end GlobalTheory.CompanionTheory.SiegelND.Coef
