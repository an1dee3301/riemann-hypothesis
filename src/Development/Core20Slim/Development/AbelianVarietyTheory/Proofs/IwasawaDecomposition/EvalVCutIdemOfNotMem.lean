module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSelfDualAtScaled
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.ByCases
public import Init.Classical
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.LevelClosure

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU Filter Topology

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


open Classical in
def cutIdem (T : Finset (HeightOneSpectrum (𝓞 F))) : Af F :=
  ⟨fun v => if v ∈ T then 1 else 0, Eventually.of_forall fun v => by
    by_cases h : v ∈ T
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

theorem evalV_cutIdem_of_mem {T : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ T) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) = 1 := by
  classical
  exact if_pos h

theorem evalV_cutIdem_of_notMem {T : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ T) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) = 0 := by
  classical
  exact if_neg h

theorem tendsto_cutIdem_mul (a : Af F) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => cutIdem T * a) atTop (𝓝 a) := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | a v ∈ v.adicCompletionIntegers F}
  have hle : (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ principal S := by
    rw [le_principal_iff]; exact a.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (principal S)
  let f : Finset (HeightOneSpectrum (𝓞 F)) → P := fun T =>
    ⟨fun v => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) * a v, by
      rw [eventually_principal]
      intro w hw
      by_cases h : w ∈ T
      · simp only [evalV_cutIdem_of_mem h, one_mul]; exact hw
      · simp only [evalV_cutIdem_of_notMem h, zero_mul]; exact zero_mem _⟩
  let a' : P := ⟨fun v => a v, by rw [eventually_principal]; exact fun w hw => hw⟩
  have hf : Tendsto f atTop (𝓝 a') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change a v = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) * a v
    rw [evalV_cutIdem_of_mem this, one_mul]
  exact ((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf

theorem tendsto_cutIdem_smul (z : Af F ⊗[F] E) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => (cutIdem T : Af F) • z) atTop (𝓝 z) := by
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  induction z using TensorProduct.induction_on with
  | zero => simpa using tendsto_const_nhds
  | add x y hx hy => simpa only [smul_add] using hx.add hy
  | tmul a x =>
    have h := (tendsto_cutIdem_mul a).smul_const ((1 : Af F) ⊗ₜ[F] x)
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def cutPt (T : Finset (HeightOneSpectrum (𝓞 F))) : GAd σ J →* GAd σ J := (embAt σ J T).comp (projAt σ J T)

omit [NumberField E] in
theorem map_smul_cut (v : HeightOneSpectrum (𝓞 F)) (c : Af F) (z : Af F ⊗[F] E) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (c • z) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v c • Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  | tmul a x => simp [TensorProduct.smul_tmul']

omit [NumberField E] in
theorem cutPt_entry (T : Finset (HeightOneSpectrum (𝓞 F))) (g : GAd σ J) (i j : Fin n) :
    (matHom _ σ J (projFin σ J (cutPt σ J T g))).1 i j =
      (cutIdem T : Af F) • ((matHom _ σ J (projFin σ J g)).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j) +
        (1 : Matrix (Fin n) (Fin n) _) i j := by
  refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v => ?_
  have e : ∀ g : GAd σ J, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      ((matHom _ σ J (projFin σ J g)).1 i j) = (matHom _ σ J (proj σ J v g)).1 i j := fun g => by
    rw [← projFinLoc_projFin]; rfl
  have e1 : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      ((1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  change Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) _ =
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) _
  rw [map_add (f := _), map_smul_cut, map_sub, e, e, e1]
  by_cases hv : v ∈ T
  · have : proj σ J v (cutPt σ J T g) = proj σ J v g := proj_embAt σ J T _ ⟨v, hv⟩
    rw [this, evalV_cutIdem_of_mem hv, one_smul, sub_add_cancel]
  · have : proj σ J v (cutPt σ J T g) = 1 := (mem_atPts.1 (embAt_mem σ J T _)).2 v hv
    rw [this, evalV_cutIdem_of_notMem hv, zero_smul, zero_add, map_one, Units.val_one]

theorem tendsto_projFin_cutPt (g : GAd σ J) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => projFin σ J (cutPt σ J T g)) atTop (𝓝 (projFin σ J g)) := by
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  have h : ∀ g : GAd σ J, Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      (matHom _ σ J (projFin σ J (cutPt σ J T g))).1) atTop (𝓝 (matHom _ σ J (projFin σ J g)).1) := fun g => by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    simp only [cutPt_entry]
    have := (tendsto_cutIdem_smul ((matHom _ σ J (projFin σ J g)).1 i j -
      (1 : Matrix (Fin n) (Fin n) _) i j)).add_const ((1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j)
    rwa [sub_add_cancel] at this
  rw [(isEmbedding_matHom _ σ J).tendsto_nhds_iff, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h g).prodMk_nhds ?_
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  have h2 := h g⁻¹
  simp only [map_inv] at h2
  exact h2

theorem tendsto_cutPt {g : GAd σ J} (hg : g ∈ finPts σ J) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => cutPt σ J T g) atTop (𝓝 g) := by
  have e : ∀ g ∈ finPts σ J, ofFin σ J (projFin σ J g) = g := fun g hg =>
    ext_inf_fin σ J (by simp [mem_finPts.1 hg]) (by simp)
  have h := ((continuous_ofFin σ J).tendsto _).comp (tendsto_projFin_cutPt σ J g)
  rw [e g hg] at h
  exact h.congr fun T => e _ (mem_atPts.1 (embAt_mem σ J T _)).1

theorem mem_of_isClosed {H : Subgroup (GAd σ J)} (hH : IsClosed (H : Set (GAd σ J))) {g : GAd σ J}
    (hg : g ∈ finPts σ J) (h : ∀ v, emb σ J v (proj σ J v g) ∈ H) : g ∈ H :=
  hH.mem_of_tendsto (tendsto_cutPt σ J hg) (Eventually.of_forall fun T =>
    Subgroup.noncommProd_mem H (f := fun v : T => emb σ J v (proj σ J v g))
      (fun _ _ _ _ h => commute_emb σ J _ (proj_emb_ne σ J (fun e => h (Subtype.ext e)) _)) fun v _ => h v)

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.WeilParts
attribute [local instance] Formalism.BasicNotions.Host.cmStar


end GlobalTheory.LevelClosure

end
