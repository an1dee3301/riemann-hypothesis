module

public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrConjApply
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.CoefMod
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
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
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

namespace GlobalTheory.FrameColSmul

theorem colMul_mem_of_span {A : Type} [CommRing A] (S : Subring A) {ι : Type} (M : Submodule S (ι → A))
    (c : ι → A) (G : Set A) (hG : ∀ y ∈ G, (fun i => c i * y) ∈ M) (x : A)
    (hx : x ∈ Submodule.span S G) : (fun i => c i * x) ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hG y hy
  | zero =>
    have : (fun i => c i * (0 : A)) = 0 := by funext i; simp
    rw [this]; exact M.zero_mem
  | add a b _ _ ha hb =>
    have : (fun i => c i * (a + b)) = (fun i => c i * a) + (fun i => c i * b) := by
      funext i; simp [mul_add]
    rw [this]; exact M.add_mem ha hb
  | smul r a _ ha =>
    have : (fun i => c i * (r • a)) = r • (fun i => c i * a) := by
      funext i
      show c i * ((r : A) * a) = (r : A) * (c i * a)
      exact mul_left_comm _ _ _
    rw [this]; exact M.smul_mem r ha

theorem mulVec_eq_sum_col {A : Type} [CommRing A] {n : ℕ} (P : Matrix (Fin n) (Fin n) A) (w : Fin n → A) :
    P *ᵥ w = ∑ j, (fun i => P i j * w j) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply]

theorem map_col_mul {E A : Type} [Field E] [NumberField E] [CommRing A] (φ : E →+* A) {n : ℕ}
    (c : Fin n → E) (b : 𝓞 E) :
    (fun i => φ (c i) * φ (b : E)) = fun i => φ ((b • c) i) := by
  funext i
  show _ = φ ((b : E) * c i)
  rw [map_mul, mul_comm]

theorem gen_mem {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (j : Fin n)
    (b : 𝓞 D.host.E) (hb : b ∈ 𝔪) :
    (fun i => GlobalTheory.FrameTransport.inclEAf D ((fr : Matrix (Fin n) (Fin n) D.host.E) i j) *
        GlobalTheory.FrameTransport.inclEAf D (b : D.host.E)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  have hcol : (fun i => (fr : Matrix (Fin n) (Fin n) D.host.E) i j) ∈ colLat fr :=
    Submodule.subset_span ⟨j, rfl⟩
  have hm : b • (fun i => (fr : Matrix (Fin n) (Fin n) D.host.E) i j) ∈ 𝔪 • colLat fr :=
    Submodule.smul_mem_smul hb hcol
  rw [map_col_mul]
  exact Submodule.subset_span ⟨_, hm, rfl⟩

theorem mulVec_mem : ∀ {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin n → Lev.EAf D), (∀ i, w i ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E) ((fun b : 𝓞 D.host.E => GlobalTheory.FrameTransport.inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) → (Formalism.UG.bc (GlobalTheory.FrameTransport.inclEAf D) fr).val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  intro D n fr 𝔪 w hw
  rw [mulVec_eq_sum_col]
  refine Submodule.sum_mem _ fun j _ => ?_
  exact colMul_mem_of_span (Formalism.L2.Herm.intAf D.host.F D.host.E) _
    (fun i => GlobalTheory.FrameTransport.inclEAf D ((fr : Matrix (Fin n) (Fin n) D.host.E) i j)) _
    (by
      rintro _ ⟨b, hb, rfl⟩
      exact gen_mem fr 𝔪 j b hb) (w j) (hw j)

end GlobalTheory.FrameColSmul
