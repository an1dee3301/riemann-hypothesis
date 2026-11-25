module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.HformZeroRight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementC
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult  Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker 
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameIdeal

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def InId (I : Ideal (𝓞 E)) (x : E ⊗[F] Formalism.L2.Herm.Af F) : Prop :=
  ∃ s ∈ Formalism.L2.DIV.idS F I, (s : E ⊗[F] Formalism.L2.Herm.Af F) = x

theorem inId_zero (I : Ideal (𝓞 E)) : InId (F := F) I 0 := ⟨0, zero_mem _, rfl⟩

theorem inId_add {I : Ideal (𝓞 E)} {x y : E ⊗[F] Formalism.L2.Herm.Af F} (hx : InId I x) (hy : InId I y) :
    InId I (x + y) := by
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  exact ⟨s + t, add_mem hs ht, rfl⟩

theorem inId_mul {I : Ideal (𝓞 E)} {t x : E ⊗[F] Formalism.L2.Herm.Af F} (ht : t ∈ Formalism.L2.Herm.intAf F E)
    (hx : InId I x) : InId I (t * x) := by
  obtain ⟨s, hs, rfl⟩ := hx
  exact ⟨⟨t, ht⟩ * s, Ideal.mul_mem_left _ _ hs, rfl⟩

theorem inId_sum {I : Ideal (𝓞 E)} {n : ℕ} (f : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (h : ∀ i, InId I (f i)) :
    InId I (∑ i, f i) := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simpa using inId_zero (F := F) I
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact inId_add (h a) ih

theorem inId_int {I : Ideal (𝓞 E)} {x : E ⊗[F] Formalism.L2.Herm.Af F} (hx : InId I x) :
    x ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨s, -, rfl⟩ := hx
  exact s.2

theorem mulVec_eq_sum {A : Type} [CommRing A] {n : ℕ} (B : Matrix (Fin n) (Fin n) A) (u : Fin n → A) :
    B *ᵥ u = ∑ i, u i • (B *ᵥ Pi.single i 1) := by
  funext c
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Matrix.mulVec_single_one, smul_eq_mul, Matrix.transpose_apply]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem smul_mem_hatL_ideal {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) {𝔪 : Ideal (𝓞 E)}
    {a : 𝓞 E} (ha : a ∈ 𝔪) {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F} (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E a) • z ∈
      Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    refine Submodule.subset_span ⟨a • l, Submodule.smul_mem_smul ha hl, ?_⟩
    funext i
    simp [Algebra.smul_def]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

theorem idS_smul_mem_hatL {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) {I : Ideal (𝓞 E)}
    {s : Formalism.L2.Herm.intAf F E} (hs : s ∈ Formalism.L2.DIV.idS F I) {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    (s : E ⊗[F] Formalism.L2.Herm.Af F) • z ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ) := by
  unfold Formalism.L2.DIV.idS Ideal.map at hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact smul_mem_hatL_ideal Λ ha hz
  | zero => simp
  | add x y _ _ hx hy => rw [Subring.coe_add, add_smul]; exact Submodule.add_mem _ hx hy
  | smul t x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, mul_smul]
    exact Submodule.smul_mem _ t hx

theorem mem_hatL_smul_iff {n : ℕ} (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (I : Ideal (𝓞 E)) (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    v ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ) ↔ ∀ i, InId I (((β⁻¹).1 *ᵥ v) i) := by
  constructor
  · intro hv
    unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, rfl⟩ := hw
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr l hl i
        have e : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((r • l) i)) =
            Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E r) •
              (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)) := by
          funext i
          simp [Algebra.smul_def]
        beta_reduce
        rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
        have hl' := (hfr _).1 (Submodule.subset_span ⟨l, hl, rfl⟩) i
        exact ⟨Formalism.L2.DIV.oToS F E r * ⟨_, hl'⟩, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr), rfl⟩
      · intro x y hx hy i
        have e : (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((x + y) i)) =
            (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) +
              (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (y i)) := by
          funext i
          simp
        beta_reduce at hx hy ⊢
        rw [e, Matrix.mulVec_add, Pi.add_apply]
        exact inId_add (hx i) (hy i)
    | zero => intro i; rw [Matrix.mulVec_zero]; exact inId_zero I
    | add x y _ _ hx hy => intro i; rw [Matrix.mulVec_add, Pi.add_apply]; exact inId_add (hx i) (hy i)
    | smul t x _ hx =>
      intro i
      rw [Subring.smul_def, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      exact inId_mul t.2 (hx i)
  · intro hu
    have e1 : v = β.1 *ᵥ ((β⁻¹).1 *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e1, mulVec_eq_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨s, hs, hsv⟩ := hu i
    rw [← hsv]
    refine idS_smul_mem_hatL Λ hs ((hfr _).2 fun k => ?_)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _

end General

variable {D : D7}


def cO (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E :=
  NumberField.RingOfIntegers.mapRingHom (D.sp.cm.sig : D.host.E →+* D.host.E)


def sO (D : D7) : Formalism.L2.Herm.intAf D.host.F D.host.E →+* Formalism.L2.Herm.intAf D.host.F D.host.E :=
  (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)).restrict _ _ (fun _ hs => GlobalTheory.LevSplit.sigR_int hs)

theorem sO_comp_oToS : (sO D).comp (Formalism.L2.DIV.oToS D.host.F D.host.E) = (Formalism.L2.DIV.oToS D.host.F D.host.E).comp (cO D) := by
  ext b
  exact GlobalTheory.GramFrame.sigR_inclE (D := D) (b : D.host.E)



theorem inId_sigR {I K : Ideal (𝓞 D.host.E)} (hIK : I.map (cO D) ≤ K) {x : Lev.EAf D} (hx : InId (F := D.host.F) I x) :
    InId (F := D.host.F) K (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) x) := by
  obtain ⟨s, hs, rfl⟩ := hx
  refine ⟨sO D s, ?_, ?_⟩
  · have h1 : sO D s ∈ (Formalism.L2.DIV.idS D.host.F I).map (sO D) := Ideal.mem_map_of_mem _ hs
    have h2 : (Formalism.L2.DIV.idS D.host.F I).map (sO D) ≤ Formalism.L2.DIV.idS D.host.F K := by
      unfold Formalism.L2.DIV.idS
      rw [Ideal.map_map, sO_comp_oToS, ← Ideal.map_map]
      exact Ideal.map_mono hIK
    exact h2 h1
  · first
      | exact RingHom.coe_restrict_apply _ _ _ _ s
      | exact congrArg Subtype.val (RingHom.restrict_apply _ _ s)
      | (unfold sO; rw [RingHom.restrict_apply])
      | (with_reducible_and_instances rfl)

end GlobalTheory.FrameIdeal

namespace GlobalTheory.FrameIdeal

variable {D : D7}

local notation "σA" => Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)
local notation "ιA" => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)












end GlobalTheory.FrameIdeal

