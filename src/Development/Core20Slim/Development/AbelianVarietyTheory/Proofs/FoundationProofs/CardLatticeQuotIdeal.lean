module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.Core20Slim.Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.PolarLatticePairs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelic
public import Development.Core20Slim.Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormEqRelIndexMul
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Function
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Quot
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

open NumberField IsDedekindDomain Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MatrixLatticeIndex

theorem card_matIn (D : D7) (a d : ℕ) (A B : Submodule (𝓞 D.host.E) D.host.E) :
    Nat.card (matIn D a d A ⧸ (matIn D a d B).addSubgroupOf (matIn D a d A)) =
      (B.toAddSubgroup.relIndex A.toAddSubgroup) ^ (a * d) := by
  let Q := A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup
  let f : matIn D a d A →+ (Fin d → Fin a → Q) :=
    { toFun := fun z i j => QuotientAddGroup.mk (⟨z.1 i j, z.2 i j⟩ : A.toAddSubgroup)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := by
    intro y
    refine ⟨⟨fun i j => ((y i j).out : A.toAddSubgroup), fun i j => (y i j).out.2⟩, ?_⟩
    funext i j
    exact QuotientAddGroup.out_eq' (y i j)
  have hker : f.ker = (matIn D a d B).addSubgroupOf (matIn D a d A) := by
    ext z
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h i j
      exact (QuotientAddGroup.eq_zero_iff _).1 (congrFun (congrFun h i) j)
    · intro h
      funext i j
      exact (QuotientAddGroup.eq_zero_iff _).2 (h i j)
  rw [← hker, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv,
    Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a), Nat.card_eq_fintype_card (α := Fin d),
    Fintype.card_fin, Fintype.card_fin, ← pow_mul]
  rfl

theorem relIndex_smul {K : Type} [Field K] [NumberField K]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hJ : J ≠ 0) (q : Ideal (𝓞 K)) (hq : q ≠ ⊥) :
    (q • (J : Submodule (𝓞 K) K)).toAddSubgroup.relIndex (J : Submodule (𝓞 K) K).toAddSubgroup =
      Ideal.absNorm q := by
  have hq' : (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hq
  have hle : (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J ≤ J := by
    calc (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J ≤ 1 * J :=
          mul_le_mul' FractionalIdeal.coeIdeal_le_one le_rfl
      _ = J := one_mul J
  have h := Formalism.L2.LamCM.Dx.absNorm_eq_relIndex_mul J _ (mul_ne_zero hq' hJ) hle
  have he : (((q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) = q • (J : Submodule (𝓞 K) K) := by
    apply le_antisymm
    · rw [FractionalIdeal.coe_mul]
      refine Submodule.mul_le.2 fun x hx y hy => ?_
      obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem_smul hb hy
    · refine Submodule.smul_le.2 fun b hb y hy => ?_
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hb) hy
  rw [he, map_mul, FractionalIdeal.coeIdeal_absNorm] at h
  have h0 : FractionalIdeal.absNorm J ≠ 0 := fun h' => hJ (FractionalIdeal.absNorm_eq_zero_iff.1 h')
  exact_mod_cast (mul_right_cancel₀ h0 h).symm


open GlobalTheory.NormSum.MovedLattice in
theorem coefLat_eq (D : D7) (cc : Ideal (𝓞 D.host.K)) :
    coefLat D cc = ((ext D cc * D.host.AA0 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro t ⟨c, hc, m, hm, rfl⟩
    exact FractionalIdeal.mul_mem_mul (mem_ext D hc) hm
  · rw [FractionalIdeal.coe_mul]
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
    clear hx
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨c, hc, rfl⟩ := hb
      exact Submodule.subset_span ⟨c, hc, y, hy, rfl⟩
    | zero => rw [map_zero, zero_mul]; exact zero_mem _
    | add b b' _ _ hb hb' => rw [map_add (f := _), add_mul]; exact add_mem hb hb'
    | smul r b _ hb =>
      rw [smul_eq_mul, map_mul, mul_assoc, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r hb

end GlobalTheory.MatrixLatticeIndex

