module

public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureExists
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsInfEmbUnique
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Emb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isInfEmb_unique (τ : E →+* ℂ) {θ θ' : Ainf F ⊗[F] E →+* ℂ} (h : IsInfEmb τ θ) (h' : IsInfEmb τ θ') : θ = θ' := by
  first | exact UpperTheory.Reformulated.B.Qh26.isInfEmb_unique .. | (apply UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› ‹_› ‹_› ‹_› ‹_› τ θ θ' h h' | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› ‹_› ‹_› ‹_› ‹_› τ θ θ' h | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› ‹_› ‹_› ‹_› ‹_› τ θ θ' | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› ‹_› ‹_› ‹_› ‹_› τ θ | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› ‹_› ‹_› ‹_› ‹_› τ | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E ‹_› | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F E | exact @UpperTheory.Reformulated.B.Qh26.isInfEmb_unique F

def plF (τ : E →+* ℂ) : InfinitePlace F := InfinitePlace.mk (τ.comp (algebraMap F E))

def compF (τ : E →+* ℂ) : Ainf F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding (plF (F := F) τ)).comp
    (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) (plF (F := F) τ))

theorem compF_cont (τ : E →+* ℂ) : Continuous (compF (F := F) τ) :=
  (InfinitePlace.Completion.isometry_extensionEmbedding (plF (F := F) τ)).continuous.comp (continuous_apply _)

theorem compF_alg [IsTotallyReal F] (τ : E →+* ℂ) (x : F) : compF (F := F) τ (algebraMap F (Ainf F) x) = τ (algebraMap F E x) := by
  have h1 : compF (F := F) τ (algebraMap F (Ainf F) x) = (plF (F := F) τ).embedding x :=
    by
      change (InfinitePlace.Completion.extensionEmbedding (plF (F := F) τ))
        ((algebraMap F (Ainf F) x) (plF (F := F) τ)) = _
      rw [InfiniteAdeleRing.algebraMap_apply]
      exact InfinitePlace.Completion.extensionEmbedding_coe _ _
  rw [h1]
  have hr : ComplexEmbedding.IsReal (τ.comp (algebraMap F E)) := IsTotallyReal.complexEmbedding_isReal _
  unfold plF
  rw [InfinitePlace.embedding_mk_eq_of_isReal hr]
  rfl

def projAt [IsTotallyReal F] (τ : E →+* ℂ) : Ainf F ⊗[F] E →+* ℂ :=
  letI : Algebra F ℂ := (τ.comp (algebraMap F E)).toAlgebra
  (Algebra.TensorProduct.productMap (R := F)
    ({ compF (F := F) τ with commutes' := fun x => compF_alg τ x } : Ainf F →ₐ[F] ℂ)
    ({ τ with commutes' := fun _ => rfl } : E →ₐ[F] ℂ)).toRingHom

theorem projAt_tmul [IsTotallyReal F] (τ : E →+* ℂ) (a : Ainf F) (x : E) :
    projAt (F := F) τ (a ⊗ₜ[F] x) = compF (F := F) τ a * τ x := rfl

theorem projAt_isInfEmb [IsTotallyReal F] (τ : E →+* ℂ) : IsInfEmb τ (projAt (F := F) τ) := by
  refine ⟨fun x => by rw [projAt_tmul, map_one, one_mul], ?_⟩
  simp only [projAt_tmul, map_one, mul_one]
  exact compF_cont τ

def inlA : Ainf F →ₗ[F] AF F where
  toFun a := pairA F a 0
  map_add' a b := Prod.ext rfl (add_zero (0 : Af F)).symm
  map_smul' c a := Prod.ext rfl (smul_zero (A := Af F) c).symm

def inrA : Af F →ₗ[F] AF F where
  toFun b := pairA F 0 b
  map_add' a b := Prod.ext (add_zero (0 : Ainf F)).symm rfl
  map_smul' c a := Prod.ext (smul_zero (A := Ainf F) c).symm rfl

def pairE (a : Ainf F ⊗[F] E) (b : Af F ⊗[F] E) : AF F ⊗[F] E :=
  TensorProduct.map (inlA (F := F)) LinearMap.id a + TensorProduct.map (inrA (F := F)) LinearMap.id b

theorem pairE_eta (z : AF F ⊗[F] E) :
    pairE (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) = z := by
  unfold pairE
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul,
      LinearMap.id_apply, AlgHom.id_apply, ← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext (add_zero (fstA F a)) (zero_add (sndA F a))
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), add_add_add_comm, ha, hb]

theorem fst_pairE (a : Ainf F ⊗[F] E) (b : Af F ⊗[F] E) :
    Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairE a b) = a := by
  unfold pairE
  have h1 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (TensorProduct.map (inlA (F := F)) LinearMap.id a) = a := by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x e => rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have h2 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (TensorProduct.map (inrA (F := F)) LinearMap.id b) = 0 := by
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul x e =>
      rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
      exact TensorProduct.zero_tmul _ _
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
  rw [map_add (f := _), h1, h2, add_zero]

theorem snd_pairE (a : Ainf F ⊗[F] E) (b : Af F ⊗[F] E) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (pairE a b) = b := by
  unfold pairE
  have h1 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (TensorProduct.map (inlA (F := F)) LinearMap.id a) = 0 := by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x e =>
      rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
      exact TensorProduct.zero_tmul _ _
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
  have h2 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (TensorProduct.map (inrA (F := F)) LinearMap.id b) = b := by
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul x e => rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [map_add (f := _), h1, h2, zero_add]

end Emb

section Raw

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (cm : CMData F E) {T : Type} [Fintype T] (emb : T → E →+* ℂ) (cd : CDHaar)


end Raw

variable (D : D7)

abbrev InfF : Type := D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)

def th0 : InfF D := fun τ => haveI := D.sp.cm.totReal; projAt (F := D.host.F) (tauE D τ)

theorem theta_infinite_family : IsInfFam (D := D) (th0 D) := fun τ => haveI := D.sp.cm.totReal; projAt_isInfEmb (tauE D τ)

variable {D}

theorem fam_eq {θ : InfF D} (h : IsInfFam (D := D) θ) : θ = th0 D :=
  funext fun τ => isInfEmb_unique _ (h τ) (theta_infinite_family D τ)

theorem allSome_fam {Q : InfF D → Prop} : AllSome (IsInfFam (D := D)) Q ↔ Q (th0 D) :=
  ⟨fun h => h.2 _ (theta_infinite_family D), fun h => ⟨⟨_, theta_infinite_family D⟩, fun _ hθ => fam_eq hθ ▸ h⟩⟩

theorem ae_ext {x y : AE D} (h1 : infPart D x = infPart D y) (h2 : finPart D x = finPart D y) : x = y := by
  have key : ∀ z : AE D, pairE (infPart D z) (finPart D z) = z := fun z => pairE_eta z
  rw [← key x, ← key y, h1, h2]



end Formalism.L2.Fam.ThC

end
