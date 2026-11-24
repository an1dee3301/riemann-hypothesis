module

public import Mathlib
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
public import Development.Core20Slim.Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactModNearOfFiltration
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.FlagMeasures.CocompactOfMemIffAdelic
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwoStepUnipotentCompactModSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Ext
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Map
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Maps.Basic

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.StrongUnip

open GlobalTheory.UnipFlagCore (fam wt raise fam_st)
open GlobalTheory.UAut

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def adjF : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) →+ Matrix (Fin n) (Fin n) (Af F ⊗[F] E) where
  toFun X := J⁻¹.map (inclR (F := F) (Af F)) * cT (sigR (Af F) σ) X * J.map (inclR (F := F) (Af F))
  map_zero' := by simp [cT]
  map_add' X Y := by simp [cT, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]

def finM : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) →+* Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
  RingHom.mapMatrix (finT (F := F) (E := E)).toRingHom

omit [NumberField E] in
theorem finM_apply (X : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (i j : Fin n) : finM X i j = finT (X i j) := rfl

omit [NumberField E] in
theorem finT_inclR (x : E) : finT (inclR (F := F) (AF F) x) = inclR (F := F) (Af F) x := by
  show Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x
  simp

omit [NumberField E] in
theorem finT_sigR (x : AF F ⊗[F] E) : finT (sigR (AF F) σ x) = sigR (Af F) σ (finT x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

omit [NumberField E] in
theorem finM_adjA (X : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) : finM (adjA σ J X) = adjF σ J (finM X) := by
  have a : ∀ M : Matrix (Fin n) (Fin n) E, finM (M.map (inclR (F := F) (AF F))) = M.map (inclR (F := F) (Af F)) :=
    fun M => by
      ext i j
      rw [finM_apply, Matrix.map_apply, Matrix.map_apply, finT_inclR]
  have b : finM (cT (sigR (AF F) σ) X) = cT (sigR (Af F) σ) (finM X) := by
    ext i j
    simp only [finM_apply, cT, Matrix.transpose_apply, Matrix.map_apply, finT_sigR]
  rw [adjA_apply, map_mul, map_mul, a, a, b]
  rfl

omit [NumberField E] in
theorem mat_projFin (g : GAd σ J) : (matHom _ σ J (projFin σ J g)).1 = finM (matHom _ σ J g).1 := by
  ext r s
  exact GlobalTheory.AutFunCompare.mat_mapH σ J (sndA F) g r s

end SlopeTestRemainingChoices

theorem strong_approx_unipRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k : ℕ) (Cc : Matrix (Fin n) (Fin k) E), GlobalTheory.UAut.IsIsoCols σ J Cc → ∀ W ∈ 𝓝 (1 : GFin σ J), ∃ Q : Set (GAd σ J), IsCompact Q ∧ ∀ m ∈ unipRad σ J Cc, ∃ γ ∈ ratPts σ J, ∃ q ∈ Q, q ∈ unipRad σ J Cc ∧ projFin σ J q ∈ W ∧ m = γ * q := by
  intro F E _ _ _ _ _ σ hcm n J hJ k Cc hC W hW
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.UnipFlagCore.conj_invol hcm
  obtain ⟨L, hL, hLL⟩ := exists_dualCols hJ hσ hC
  obtain ⟨d, hdd⟩ : ∃ d : Fin k → ℕ, d = fun _ => 0 := ⟨_, rfl⟩
  have hd : ∀ j, d j < 1 := fun j => by rw [hdd]; exact Nat.one_pos
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  set φ := inclR (F := F) (E := E) (AF F) with hφ
  have he := idemA_complete hJ Cc L hL hC.2 hLL
  have hs := fam_st (adjA_mul hJ) (adjA_adjA hJ hσ) (idemA (F := F) Cc L) d 1
  have hcont : Continuous (adjA σ J) := (continuous_const.matrix_mul (continuous_id.matrix_map
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ)).matrix_transpose).matrix_mul continuous_const
  have hcontF : Continuous (adjF σ J) := (continuous_const.matrix_mul (continuous_id.matrix_map
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (Af F) σ)).matrix_transpose).matrix_mul continuous_const
  have hst0 : ∀ x ∈ (φ.mapMatrix (m := Fin n)).range, adjA σ J x ∈ (φ.mapMatrix (m := Fin n)).range := by
    rintro _ ⟨X, rfl⟩; exact ⟨_, (adjA_map X).symm⟩
  have hmem := mem_unipFlag_iff_raise hJ hσ Cc L hL hC.2 hLL hd
  have hadj1 : adjF σ J 1 = 1 := by
    have h1 := finM_adjA σ J (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))
    rw [GlobalTheory.TwoStepUnipotent.st_one (adjA_mul hJ) (adjA_adjA hJ hσ), map_one] at h1
    exact h1.symm
  let fF : GFin σ J → _ := fun g => Units.embedProduct _ (matHom _ σ J g)
  have hfF : Topology.IsInducing fF := Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal
  obtain ⟨O, hO, hOW⟩ := Filter.mem_comap.1 (hfF.nhds_eq_comap 1 ▸ hW)
  let G : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) → _ := fun x => (x, MulOpposite.op (adjF σ J x))
  have hG : Continuous G := continuous_id.prodMk (MulOpposite.continuous_op.comp hcontF)
  have hD : G ⁻¹' O ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :=
    hG.continuousAt.preimage_mem_nhds (by
      have : G 1 = fF 1 := Prod.ext rfl (by
        show MulOpposite.op (adjF σ J 1) = MulOpposite.op 1
        rw [hadj1])
      rw [this]; exact hO)
  have hproj : ∀ g : GAd σ J, finM (matHom _ σ J g).1 ∈ G ⁻¹' O → projFin σ J g ∈ W := fun g hg => hOW (by
    have e : fF (projFin σ J g) = G (finM (matHom _ σ J g).1) := by
      refine Prod.ext (mat_projFin σ J g) ?_
      show MulOpposite.op (matHom _ σ J (projFin σ J g)⁻¹).1 = MulOpposite.op (adjF σ J _)
      rw [← map_inv, mat_projFin, ← finM_adjA]
      congr 2
      exact (adjA_mat hJ g).symm
    show fF (projFin σ J g) ∈ O
    rw [e]; exact hg)
  obtain ⟨V, hV, H⟩ := compact_mod_near_of_weights (st := adjA σ J) (w := wt d 1)
    (ε := fam (adjA σ J) (idemA Cc L)) (φ.mapMatrix (m := Fin n)).range
    (Matrix.scalar _ (φ (1 / 2))) hcont (adjA_mul hJ) (adjA_adjA hJ hσ) hst0
    ⟨Matrix.scalar _ (1 / 2), by ext i j; by_cases h : i = j <;> simp [h]⟩
    (by rw [← map_add (f := _), ← map_add (f := _), add_halves, map_one, map_one])
    (fun x => (Matrix.scalar_commute _ (fun _ => Commute.all _ _) x).eq) he
    (by
      have hu : ∀ j, idemA (F := F) Cc L j ∈ (φ.mapMatrix (m := Fin n)).range := fun j => ⟨_, rfl⟩
      have hv : ∀ j : Fin k ⊕ Fin k, Sum.elim (idemA (F := F) Cc L) (fun j => adjA σ J (idemA Cc L j)) j ∈
          (φ.mapMatrix (m := Fin n)).range := by
        rintro (j | j)
        exacts [hu j, hst0 _ (hu j)]
      rintro (_ | j)
      exacts [sub_mem (one_mem _) (sum_mem fun j _ => hv j), hv j]) hs
    finM (adjF σ J) hcontF (finM_adjA σ J) _ hD
  obtain ⟨W₀, hW₀, hW₀V⟩ := exists_entry_nhds V hV
  obtain ⟨K, hK, hKW, hKs⟩ := fine_cover (E := E) W₀ hW₀
  obtain ⟨K', hK', hKD, k1, k2⟩ := H (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => K)
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK)
    (fun x hx => hW₀V _ fun i j => hKW _ (hx i trivial j trivial))
    (fun X => by
      choose y hy using fun i j => hKs (X i j)
      exact ⟨_, ⟨Matrix.of y, rfl⟩, fun i _ j _ => hy i j⟩)
  let lift : ∀ x : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), (adjA σ J x * x = 1 ∧ x * adjA σ J x = 1) ∧
      x - 1 ∈ raise (fam (adjA σ J) (idemA Cc L)) (wt d 1) 0 → unipFlag σ J Cc d := fun x hx =>
    ⟨⟨⟨x, adjA σ J x, hx.1.2, hx.1.1⟩, (adjA_mul_self_iff hJ _).1 hx.1.1⟩, (hmem _).2 hx.2⟩
  let f : unipFlag σ J Cc d → _ := fun m => Units.embedProduct _ (matHom _ σ J m.1)
  have hf : Topology.IsInducing f :=
    Units.isInducing_embedProduct.comp (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)
  have hconst : unipFlag σ J Cc d = unipRad σ J Cc := by rw [hdd]; exact unipFlag_const Cc 0
  refine ⟨Subtype.val '' (f ⁻¹' ((fun x => (x, MulOpposite.op (adjA σ J x))) '' K')),
    (hf.isCompact_preimage' (hK'.image (continuous_id.prodMk (MulOpposite.continuous_op.comp hcont))) ?_).image
      continuous_subtype_val, fun m hm => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨lift x (k1 x hx), rfl⟩
  · rw [← hconst] at hm
    have hu := (adjA_mul_self_iff hJ _).2 m.2
    obtain ⟨γ, ⟨a, ha⟩, p1, k, hk, p2⟩ := k2 (matHom _ σ J m).1 ⟨⟨hu, mul_eq_one_comm.1 hu⟩, (hmem _).1 hm⟩
    obtain ⟨b, hb⟩ := hst0 γ ⟨a, ha⟩
    have e : (⟨m, hm⟩ : unipFlag σ J Cc d) = lift γ p1 * lift k (k1 k hk) := Subtype.ext (Subtype.ext (Units.ext p2))
    refine ⟨(lift γ p1).1, ?_, (lift k (k1 k hk)).1, ⟨lift k (k1 k hk), ⟨k, hk, rfl⟩, rfl⟩,
      hconst ▸ (lift k (k1 k hk)).2, hproj _ (hKD k hk), congrArg Subtype.val e⟩
    have inj : Function.Injective (φ.mapMatrix (m := Fin n)) := Matrix.map_injective GlobalTheory.AutFunCompare.inclA_injective
    have hab : a * b = 1 := inj (by rw [map_mul, ha, hb, map_one, p1.1.2])
    refine ⟨⟨a, b, hab, mul_eq_one_comm.1 hab⟩, inj ?_, Units.ext ha⟩
    have hγ' : cT (sigR (AF F) σ) γ * J.map φ * γ = J.map φ := (lift γ p1).1.2
    rw [← ha] at hγ'
    rw [map_mul, map_mul]
    exact (congrArg (· * J.map φ * a.map φ) (GlobalTheory.AutFunCounterexample.cT_map_gen σ a).symm).trans hγ'

end GlobalTheory.CompanionTheory.StrongUnip

end
