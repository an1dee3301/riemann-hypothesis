module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrConjApply
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.StatementC
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.HatIdealCarry

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def intOf (b : 𝓞 E) : Formalism.L2.Herm.intAf F E :=
  ⟨Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E b),
    Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E b, b, rfl⟩, rfl⟩)⟩

theorem incl_smul (b : 𝓞 E) (l : Fin n → E) :
    (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((b • l) i)) =
      intOf (F := F) b • (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)) := by
  funext i
  show _ = Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (algebraMap (𝓞 E) E b) *
    Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (l i)
  rw [← map_mul, Pi.smul_apply, Algebra.smul_def]

theorem incl_add (a b : Fin n → E) :
    (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((a + b) i)) =
      (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (a i)) +
        (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (b i)) := by
  funext i
  exact map_add _ (a i) (b i)

theorem mulVec_intSmul (M : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (r : Formalism.L2.Herm.intAf F E) (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    M *ᵥ (r • v) = r • (M *ᵥ v) := by
  have e : r • v = (r : E ⊗[F] Formalism.L2.Herm.Af F) • v := rfl
  have e' : r • (M *ᵥ v) = (r : E ⊗[F] Formalism.L2.Herm.Af F) • (M *ᵥ v) := rfl
  rw [e, e', Matrix.mulVec_smul]

theorem intOf_smul_mem (Λ : Submodule (𝓞 E) (Fin n → E))
    (𝔪 : Ideal (𝓞 E)) {b : 𝓞 E} (hb : b ∈ 𝔪) (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    intOf (F := F) b • z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  refine Submodule.span_induction
    (p := fun z _ => intOf (F := F) b • z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.subset_span ⟨b • x, Submodule.smul_mem_smul hb hx, ?_⟩
    exact incl_smul b x
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a c _ _ ha hc
    rw [smul_add]; exact Submodule.add_mem _ ha hc
  · intro c a _ ha
    rw [smul_comm]; exact Submodule.smul_mem _ c ha

theorem transportGen (uf : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L Λ : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := F) L → uf *ᵥ v ∈ Formalism.L2.Herm.hatL (F := F) Λ)
    (𝔪 : Ideal (𝓞 E)) (y : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • L)) : uf *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
  have gen : ∀ w ∈ 𝔪 • L, uf *ᵥ (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (w i)) ∈
      Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ) := by
    intro w hw
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro b hb l hl
      rw [incl_smul b l, mulVec_intSmul]
      exact intOf_smul_mem Λ 𝔪 hb _ (hL _ (Submodule.subset_span ⟨l, hl, rfl⟩))
    · intro a c ha hc
      rw [incl_add, Matrix.mulVec_add]
      exact Submodule.add_mem _ ha hc
  refine Submodule.span_induction
    (p := fun y _ => uf *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨w, hw, rfl⟩
    exact gen w hw
  · rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  · intro a c _ _ ha hc
    rw [Matrix.mulVec_add]; exact Submodule.add_mem _ ha hc
  · intro c a _ ha
    rw [mulVec_intSmul]; exact Submodule.smul_mem _ c ha

end Gen

theorem transport : ∀ {D : D7} {n : ℕ} (uf : GL (Fin n) (Lev.EAf D)) (L Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (y : Fin n → Lev.EAf D), y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • L) → uf.val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) :=
  fun uf L Λ hL 𝔪 y hy => transportGen uf.val L Λ hL 𝔪 y hy

end GlobalTheory.HatIdealCarry
