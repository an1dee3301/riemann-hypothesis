module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Batteries.Logic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataLevel
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Fin.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.SetNotation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JacClosed

open GlobalTheory.MixModel.HypDec

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

def uniOnX (d : HypDec S S₀ ρ) : Set (GA D S) :=
  {g | mt S g ⬝ d.jX = d.jX ⬝ blockX d g ∧ (∀ i j : Fin ρ, j < i → blockX d g i j = 0) ∧ ∀ i, blockX d g i i = 1}

theorem t2Space_cm_host_adeles : T2Space (AE D) := by
  haveI : T2Space (Mx D 1 1) := (lattice_Mx D 1 1).2.2.2.1
  exact @T2Space.of_injective_continuous _ _ _ _ this (fun a : AE D => (Matrix.of fun _ _ => a : Mx D 1 1))
    (fun a b h => congrFun (congrFun h 0) 0) (continuous_pi fun _ => continuous_pi fun _ => continuous_id)

theorem isClosed_uniOnX (d : HypDec S S₀ ρ) : IsClosed (uniOnX d) := by
  haveI : T2Space (AE D) := t2Space_cm_host_adeles
  have hm := GlobalTheory.MixModel.continuous_mt (D := D) S
  have hb : Continuous fun g : GA D S => blockX d g := continuous_const.matrix_mul (hm.matrix_mul continuous_const)
  have e1 : {g : GA D S | ∀ i j : Fin ρ, j < i → blockX d g i j = 0} =
      ⋂ i : Fin ρ, ⋂ j : Fin ρ, ⋂ (_ : j < i), {g | blockX d g i j = 0} := by ext; simp only [Set.mem_setOf_eq, Set.mem_iInter]
  have e2 : {g : GA D S | ∀ i : Fin ρ, blockX d g i i = 1} = ⋂ i : Fin ρ, {g | blockX d g i i = 1} := by ext; simp only [Set.mem_setOf_eq, Set.mem_iInter]
  have c1 : IsClosed {g : GA D S | ∀ i j : Fin ρ, j < i → blockX d g i j = 0} := by
    rw [e1]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply j).comp ((continuous_apply i).comp hb)) continuous_const
  have c2 : IsClosed {g : GA D S | ∀ i : Fin ρ, blockX d g i i = 1} := by
    rw [e2]
    exact isClosed_iInter fun i => isClosed_eq ((continuous_apply i).comp ((continuous_apply i).comp hb)) continuous_const
  exact (isClosed_eq (hm.matrix_mul continuous_const) (continuous_const.matrix_mul hb)).inter (c1.inter c2)

theorem mem_uniOnX_of (d : HypDec S S₀ ρ) {g : GA D S} {u : GL (Fin ρ) (AE D)} (hu : u ∈ upperUni ρ (AE D))
    (h : mt S g ⬝ d.jX = d.jX ⬝ u.1) : g ∈ uniOnX d := by
  have hb : blockX d g = u.1 := by rw [blockX, h, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
  refine ⟨by rw [hb]; exact h, fun i j hij => ?_, fun i => ?_⟩
  · rw [hb]; exact (hu i j).1 hij
  · rw [hb]; exact (hu i i).2

def uniOnXSub (d : HypDec S S₀ ρ) : Subgroup (GA D S) where
  carrier := {g | ∃ u ∈ UX D ρ, mt S g ⬝ d.jX = d.jX ⬝ u.1}
  one_mem' := ⟨1, one_mem _, by rw [mt_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩
  mul_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨v, hv, hb⟩
    exact ⟨u * v, mul_mem hu hv, by
      rw [mt_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc, Units.val_mul]⟩
  inv_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨u⁻¹, inv_mem hu, ?_⟩
    have h1 : mt S a⁻¹ ⬝ d.jX ⬝ u.1 = d.jX := by
      rw [Matrix.mul_assoc, ← ha, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    calc mt S a⁻¹ ⬝ d.jX = mt S a⁻¹ ⬝ d.jX ⬝ (u.1 ⬝ (u⁻¹).1) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = d.jX ⬝ (u⁻¹).1 := by rw [← Matrix.mul_assoc, h1]

def uniUnit (U : Mx D ρ ρ) (h0 : ∀ i j : Fin ρ, j < i → U i j = 0) (h1 : ∀ i, U i i = 1) : GL (Fin ρ) (AE D) :=
  Matrix.nonsingInvUnit U (by
    rw [Matrix.det_of_upperTriangular (fun i j (h : j < i) => h0 i j h)]
    simp [h1])

theorem uniUnit_val (U : Mx D ρ ρ) (h0 : ∀ i j : Fin ρ, j < i → U i j = 0) (h1 : ∀ i, U i i = 1) :
    (uniUnit U h0 h1).1 = U := rfl

theorem uniUnit_mem (U : Mx D ρ ρ) (h0 : ∀ i j : Fin ρ, j < i → U i j = 0) (h1 : ∀ i, U i i = 1) :
    uniUnit U h0 h1 ∈ upperUni ρ (AE D) := fun i j => ⟨h0 i j, h1 i⟩

theorem flagN_le (d : HypDec S S₀ ρ) : flagN d ≤ uniOnXSub d := by
  show Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  rintro g ⟨hX, -⟩
  choose a ha1 ha2 using hX
  let A : Mx D ρ ρ := Matrix.of fun j i => a i j
  have hcol : subOne S g ⬝ d.jX = d.jX ⬝ A := by
    ext k i
    exact congrFun (ha2 i) k
  have h0 : ∀ i j : Fin ρ, j < i → (1 + A) i j = 0 := fun i j h => by
    simp only [Matrix.add_apply, A, Matrix.of_apply, Matrix.one_apply_ne h.ne', ha1 j i h.le, add_zero]
  have h1 : ∀ i, (1 + A) i i = 1 := fun i => by
    simp only [Matrix.add_apply, A, Matrix.of_apply, Matrix.one_apply_eq, ha1 i i le_rfl, add_zero]
  refine ⟨uniUnit (1 + A) h0 h1, uniUnit_mem _ h0 h1, ?_⟩
  rw [uniUnit_val, Matrix.mul_add, Matrix.mul_one, ← hcol, GlobalTheory.MixModel.HypDec.subOne_mul, add_sub_cancel]

theorem jacGrp_le (d : HypDec S S₀ ρ) : jacGrp d ≤ uniOnXSub d := by
  refine sup_le (flagN_le d) ?_
  rintro _ ⟨h, rfl⟩
  exact ⟨1, one_mem _, by rw [wittDecomp_anisotropicEmbedding_inclX, Units.val_one, Matrix.mul_one]⟩


set_option maxHeartbeats 2000000 in
theorem mem_jacGrp_of_fix (d : HypDec S S₀ ρ) {g : GA D S} (hg : mt S g ⬝ d.jX = d.jX) : g ∈ jacGrp d := by
  have hU : adj (mt S g) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = gA S ⬝ d.j0 := cancel₃ (mt_unitary S g) d.j0
  have hY : d.pY ⬝ (mt S g ⬝ d.j0) = 0 := by
    have h1 : adj d.jX ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = adj (mt S g ⬝ d.jX) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) := by rw [hg]
    rw [d.pY_eq, Matrix.mul_assoc, h1, adj_mul, Matrix.mul_assoc, hU, d.wittDecomp_gram_X_anisotropic]
  obtain ⟨b, hb⟩ : ∃ b, d.pX ⬝ (mt S g ⬝ d.j0) = b := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, d.p0 ⬝ (mt S g ⬝ d.j0) = A := ⟨_, rfl⟩
  have hdec : mt S g ⬝ d.j0 = d.jX ⬝ b + d.j0 ⬝ A := by
    have he : (d.jX ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ d.pY) ⬝ (mt S g ⬝ d.j0) = (1 : Mx D S.rank S.rank) ⬝ (mt S g ⬝ d.j0) := by rw [d.sum_eq_one]
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hY, hb, hA, Matrix.mul_zero, add_zero] at he
    exact he.symm
  have hAu : adj A * (gA S₀ * A) = gA S₀ := by
    have h1 : adj (mt S g ⬝ d.j0) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = gA S₀ := by
      rw [adj_mul, Matrix.mul_assoc, hU, d.gram_00]
    rw [hdec] at h1
    simp only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, cancel₃ d.gram_XX, cancel₃ d.wittDecomp_gram_X_anisotropic,
      cancel₃ d.gram_0X, cancel₃ d.gram_00, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] at h1
    exact h1
  obtain ⟨h, hAh⟩ : ∃ h : GA D S₀, mt S₀ h = A := ⟨ofMat S₀ A hAu, rfl⟩
  have hAi : A ⬝ mt S₀ h⁻¹ = mt S₀ 1 := by rw [← hAh, ← mt_mul, mul_inv_cancel]
  have hi : (d.emb0 h)⁻¹ = d.emb0 h⁻¹ := (map_inv d.emb0 h).symm
  have hm0 : mt S (g * d.emb0 h⁻¹) = mt S g ⬝ mt S (d.emb0 h⁻¹) := mt_mul S _ _
  have he0 : mt S (d.emb0 h⁻¹) ⬝ d.j0 = d.j0 ⬝ mt S₀ h⁻¹ := d.wittDecomp_anisotropicEmbedding_inclAnisotropic h⁻¹
  have heX : mt S (d.emb0 h⁻¹) ⬝ d.jX = d.jX := d.wittDecomp_anisotropicEmbedding_inclX h⁻¹
  have hj : d.j0 ⬝ mt S₀ (1 : GA D S₀) = d.j0 := by rw [mt_one, Matrix.mul_one]
  have hn0' : mt S (g * (d.emb0 h)⁻¹) ⬝ d.j0 = d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 := by
    have s1 : mt S (g * (d.emb0 h)⁻¹) ⬝ d.j0 = (mt S g ⬝ d.j0) ⬝ mt S₀ h⁻¹ := by
      rw [hi, hm0, Matrix.mul_assoc, he0, Matrix.mul_assoc]
    have s2 : (d.jX ⬝ b + d.j0 ⬝ A) ⬝ mt S₀ h⁻¹ = d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 ⬝ (A ⬝ mt S₀ h⁻¹) :=
      (Matrix.add_mul (d.jX ⬝ b) (d.j0 ⬝ A) (mt S₀ h⁻¹)).trans
        (congrArg₂ (· + ·) (Matrix.mul_assoc d.jX b (mt S₀ h⁻¹)) (Matrix.mul_assoc d.j0 A (mt S₀ h⁻¹)))
    have s3 : d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 ⬝ (A ⬝ mt S₀ h⁻¹) = d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 :=
      (congrArg (fun M : Mx D S₀.rank S₀.rank => d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + d.j0 ⬝ M) hAi).trans (congrArg (fun M : Mx D S.rank S₀.rank => d.jX ⬝ (b ⬝ mt S₀ h⁻¹) + M) hj)
    exact s1.trans ((congrArg (fun M : Mx D S.rank S₀.rank => M ⬝ mt S₀ h⁻¹) hdec).trans (s2.trans s3))
  have hn0 : mt S (g * (d.emb0 h)⁻¹) ⬝ d.j0 = d.j0 + d.jX ⬝ (b ⬝ mt S₀ h⁻¹) := hn0'.trans (add_comm _ _)
  have hnX' : mt S (g * (d.emb0 h)⁻¹) ⬝ d.jX = d.jX := by
    rw [hi, hm0, Matrix.mul_assoc, heX, hg]
  have hnX : mt S (g * (d.emb0 h)⁻¹) ⬝ d.jX = d.jX ⬝ (1 : GL (Fin ρ) (AE D)).1 := by
    rw [Units.val_one, Matrix.mul_one]; exact hnX'
  have hn : g * (d.emb0 h)⁻¹ ∈ flagN d := d.mem_NFlag one_mem_upperUni hnX hn0
  have hm : g * (d.emb0 h)⁻¹ * d.emb0 h ∈ jacGrp d :=
    mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)
  rwa [inv_mul_cancel_right] at hm

theorem uniOnX_subset (d : HypDec S S₀ ρ) : uniOnX d ⊆ jacGrp d := by
  rintro g ⟨hX, h0, h1⟩
  set u := uniUnit (blockX d g) h0 h1
  have hl : d.levi u ∈ flagN d := d.levi_mem_NFlag (uniUnit_mem _ h0 h1)
  have hf : mt S ((d.levi u)⁻¹ * g) ⬝ d.jX = d.jX := by
    rw [← map_inv, mt_mul, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, levi_jX, Matrix.mul_assoc,
      show (u⁻¹).1 ⬝ blockX d g = 1 from Units.inv_mul u, Matrix.mul_one]
  have := mul_mem (Subgroup.mem_sup_left (T := d.emb0.range) hl) (mem_jacGrp_of_fix d hf)
  rwa [mul_inv_cancel_left] at this

theorem jacGrp_eq (d : HypDec S S₀ ρ) : (jacGrp d : Set (GA D S)) = uniOnX d := by
  refine Set.Subset.antisymm (fun g hg => ?_) (uniOnX_subset d)
  obtain ⟨u, hu, h⟩ := jacGrp_le d hg
  exact mem_uniOnX_of d hu h

end GlobalTheory.JacClosed

namespace GlobalTheory

theorem jacGrp_isClosed : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), IsClosed (jacGrp d : Set (GA D S)) := by
  intro D S S₀ ρ d
  rw [GlobalTheory.JacClosed.jacGrp_eq]
  exact GlobalTheory.JacClosed.isClosed_uniOnX d

end GlobalTheory
