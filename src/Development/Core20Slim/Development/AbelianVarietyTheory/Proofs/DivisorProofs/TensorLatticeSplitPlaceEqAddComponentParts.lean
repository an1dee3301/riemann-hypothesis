module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
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
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.WithVal

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SplitPlaceLat

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tmul_smul_gen {n d : ℕ} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (a : Fv F v) (o : 𝓞 E) (c : AF F) (x : Fin n → E)
    (y : Fin d → E) :
    ((GlobalTheory.LatVac.liftV v a ⊗ₜ[F] (o : E) : AE F E) • (c • incM F (Matrix.vecMulVec x y))) =
      (GlobalTheory.LatVac.liftV v a * c) • incM F (Matrix.vecMulVec (o • x) y) := by
  ext i j
  simp [incM, inclR, Matrix.vecMulVec_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul',
    Algebra.smul_def, mul_assoc]

theorem tmul_smul_mem {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {a : Fv F v}
    (ha : a ∈ v.adicCompletionIntegers F) (o : 𝓞 E) :
    ∀ γ ∈ latAtV X Y v, ((GlobalTheory.LatVac.liftV v a ⊗ₜ[F] (o : E) : AE F E) • γ) ∈ latAtV X Y v := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, hc, hci, x, hx, y, hy, rfl⟩ := hz
    rw [tmul_smul_gen]
    refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a * c, ?_, ?_, o • x, X.L.smul_mem o hx, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u c, hc u hu, mul_zero]
    · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
      exact mul_mem ha hci
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_lift {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    ∃ e : AE F E, compFin F E v e = y ∧ ∀ γ ∈ latAtV X Y v, e • γ ∈ latAtV X Y v := by
  refine intLoc_induction (p := fun y => ∃ e : AE F E, compFin F E v e = y ∧ ∀ γ ∈ latAtV X Y v, e • γ ∈ latAtV X Y v)
    ?_ ?_ ?_ ?_ hy
  · intro a ha o
    refine ⟨GlobalTheory.LatVac.liftV v a ⊗ₜ[F] (o : E), ?_, tmul_smul_mem X Y v ha o⟩
    simp [compFin, GlobalTheory.LatVac.evFin_liftV]
  · exact ⟨0, map_zero _, fun γ _ => by rw [zero_smul]; exact zero_mem _⟩
  · intro y z hy hz
    obtain ⟨e, he, he'⟩ := hy
    obtain ⟨f, hf, hf'⟩ := hz
    exact ⟨e + f, by rw [map_add (f := _), he, hf], fun γ hγ => by rw [add_smul]; exact add_mem (he' γ hγ) (hf' γ hγ)⟩
  · intro y hy
    obtain ⟨e, he, he'⟩ := hy
    exact ⟨-e, by rw [map_neg, he], fun γ hγ => by rw [neg_smul]; exact neg_mem (he' γ hγ)⟩

theorem map_piW_smul {n d : ℕ} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (e : AE F E)
    (γ : Matrix (Fin n) (Fin d) (AE F E)) : (e • γ).map (piW t) = piW t e • γ.map (piW t) := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply, map_mul]

end GlobalTheory.SplitPlaceLat

namespace GlobalTheory.SplitPlaceLat

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

theorem latAtV_eq_add_parts : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      ∃ γA ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      ∃ γB ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
        γ = γA + γB ∧ γA.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧
          γB.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = 0 := by
  intro D a a' Bs Γ X om om' hTr L₁ L₂ γ hγ
  have h := hTr.base.cm
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitPlaceLat.exists_lift {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁
    (splitIdem_mem h Bs.τ₁)
  have p1 : piW Bs.τ₁ e = 1 := by
    change splitProj Bs.τ₁ (compFin _ _ _ e) = 1
    rw [he]; exact splitProj_splitIdem h _
  have p2 : piW (Bs.τ₁.comp D.sp.cm.sig) e = 0 := by
    change splitProj (Bs.τ₁.comp D.sp.cm.sig) (compFin _ _ _ e) = 0
    rw [he]; exact splitProj_comp_splitIdem h _
  refine ⟨γ - e • γ, sub_mem hγ (he' γ hγ), e • γ, he' γ hγ, (sub_add_cancel _ _).symm, ?_, ?_⟩
  · ext i j
    simp [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, map_sub, map_mul, p1]
  · rw [GlobalTheory.SplitPlaceLat.map_piW_smul, p2, zero_smul]

end GlobalTheory.SplitPlaceLat
