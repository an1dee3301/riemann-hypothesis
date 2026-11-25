module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseD
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
public import Init.Classical
public import Init.Core
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Restrict
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.ClusterPt
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Matrix Topology

namespace PositivityTheory.Rg.Sw.Glob.DenseP

variable {n : ℕ}

theorem inG_nUh {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (nU b) := by
  simp only [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]
  simp

theorem inG_mL {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A.det) : InG (fromBlocks A 0 0 (A⁻¹)ᴴ) := by
  have h1 : Aᴴ * (A⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hA, Matrix.conjTranspose_one]
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hA
  simp only [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero]
  simp [h1, h2]

def hpart (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A + Aᴴ)

theorem hpart_herm (A : Matrix (Fin n) (Fin n) ℂ) : (hpart A)ᴴ = hpart A := by
  simp only [hpart, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  rw [add_comm]
  congr 1
  simp

theorem hpart_of_herm {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : hpart b = b := by
  rw [hpart, hb, ← two_smul ℂ b, smul_smul]; norm_num

def nuE (A : Matrix (Fin n) (Fin n) ℂ) : GR n := mkGR (nU (hpart A)) (inG_nUh (hpart_herm A))

theorem continuous_hpart : Continuous (hpart (n := n)) := by
  have h : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A + Aᴴ :=
    (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)).add (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)).matrix_conjTranspose
  exact h.const_smul (1 / 2 : ℂ)

theorem nU_mul_neg (b : Matrix (Fin n) (Fin n) ℂ) : nU b * nU (-b) = 1 := by
  simp [nU, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]

theorem continuous_nU : Continuous (nU (n := n)) :=
  Continuous.matrix_fromBlocks continuous_const continuous_id continuous_const continuous_const

theorem continuous_nuE : Continuous (nuE (n := n)) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · show Continuous fun A => nU (hpart A)
    exact continuous_nU.comp continuous_hpart
  · show Continuous fun A : Matrix (Fin n) (Fin n) ℂ => (nU (hpart A))⁻¹
    have e : (fun A : Matrix (Fin n) (Fin n) ℂ => (nU (hpart A))⁻¹) = fun A => nU (-hpart A) := by
      funext A
      exact Matrix.inv_eq_right_inv (nU_mul_neg _)
    rw [e]
    exact continuous_nU.comp continuous_hpart.neg


open Classical in
def mlE (A : Matrix (Fin n) (Fin n) ℂ) : GR n :=
  if h : IsUnit A.det then mkGR (fromBlocks A 0 0 (A⁻¹)ᴴ) (inG_mL h) else 1

theorem mlE_of {A : Matrix (Fin n) (Fin n) ℂ} (h : IsUnit A.det) :
    mlE A = mkGR (fromBlocks A 0 0 (A⁻¹)ᴴ) (inG_mL h) := by
  unfold mlE; exact dif_pos h

theorem isOpen_unitDet : IsOpen {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} := by
  have : {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} = (fun A : Matrix (Fin n) (Fin n) ℂ => A.det) ⁻¹' {z | z ≠ 0} :=
    Set.ext fun A => isUnit_iff_ne_zero
  rw [this]
  exact isOpen_ne.preimage (Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)))

theorem continuousOn_inv_mat : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) {A | IsUnit A.det} := by
  have e : (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e]
  have h1 : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ => (A.det)⁻¹) {A | IsUnit A.det} :=
    ContinuousOn.inv₀ (Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) ℂ))).continuousOn
      fun A hA => isUnit_iff_ne_zero.1 hA
  have h2 : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A.adjugate :=
    Continuous.matrix_adjugate (continuous_id (X := Matrix (Fin n) (Fin n) ℂ))
  exact h1.smul h2.continuousOn

theorem inv_mL {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A.det) :
    (fromBlocks A 0 0 (A⁻¹)ᴴ)⁻¹ = fromBlocks A⁻¹ 0 0 Aᴴ := by
  refine Matrix.inv_eq_right_inv ?_
  have h1 : (A⁻¹)ᴴ * Aᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hA, Matrix.conjTranspose_one]
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.mul_nonsing_inv _ hA, h1, ← Matrix.fromBlocks_one]

theorem continuousOn_mlE : ContinuousOn (mlE (n := n)) {A | IsUnit A.det} := by
  have hind : Topology.IsInducing (fun g : GR n => Units.embedProduct _ (g : GL (Fin n ⊕ Fin n) ℂ)) :=
    Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal
  rw [hind.continuousOn_iff]
  have hi := continuousOn_inv_mat (n := n)
  have hc : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ =>
      (fromBlocks A 0 0 (A⁻¹)ᴴ, MulOpposite.op (fromBlocks A⁻¹ 0 0 Aᴴ))) {A | IsUnit A.det} := by
    rw [continuousOn_iff_continuous_restrict]
    have hi' : Continuous fun A : {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} => A.1⁻¹ := hi.restrict
    refine Continuous.prodMk ?_ ?_
    · exact Continuous.matrix_fromBlocks continuous_subtype_val continuous_const continuous_const
        hi'.matrix_conjTranspose
    · exact MulOpposite.continuous_op.comp (Continuous.matrix_fromBlocks hi' continuous_const continuous_const
        continuous_subtype_val.matrix_conjTranspose)
  refine ContinuousOn.congr hc fun A hA => ?_
  simp only [Function.comp_apply, mlE_of hA]
  show ((fromBlocks A 0 0 (A⁻¹)ᴴ), MulOpposite.op (fromBlocks A 0 0 (A⁻¹)ᴴ)⁻¹) = _
  rw [inv_mL hA]

theorem nuE_mem_closure {K : Type} [Field K] (τ : K →+* ℂ) (hτ : DenseRange τ) (A : Matrix (Fin n) (Fin n) ℂ) :
    nuE A ∈ closure (Set.range fun e : Matrix (Fin n) (Fin n) K => nuE (e.map τ)) := by
  have hd : DenseRange (fun e : Matrix (Fin n) (Fin n) K => e.map τ) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => hτ
  have h1 : nuE A ∈ nuE '' closure (Set.range fun e : Matrix (Fin n) (Fin n) K => e.map τ) := by
    rw [hd.closure_range]; exact ⟨A, trivial, rfl⟩
  have h2 := image_closure_subset_closure_image continuous_nuE h1
  rwa [← Set.range_comp] at h2

theorem mlE_mem_closure {K : Type} [Field K] (τ : K →+* ℂ) (hτ : DenseRange τ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUnit A.det) :
    mlE A ∈ closure (mlE '' ({A | IsUnit A.det} ∩ Set.range fun e : Matrix (Fin n) (Fin n) K => e.map τ)) := by
  have hd : DenseRange (fun e : Matrix (Fin n) (Fin n) K => e.map τ) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => hτ
  have hc : ContinuousAt (mlE (n := n)) A := (continuousOn_mlE (n := n)).continuousAt (isOpen_unitDet.mem_nhds hA)
  rw [mem_closure_iff_nhds]
  intro t ht
  have h1 : mlE ⁻¹' t ∩ {A | IsUnit A.det} ∈ 𝓝 A := Filter.inter_mem (hc ht) (isOpen_unitDet.mem_nhds hA)
  obtain ⟨U, hU, hUo, hAU⟩ := mem_nhds_iff.1 h1
  obtain ⟨e, he⟩ := hd.exists_mem_open hUo ⟨A, hAU⟩
  exact ⟨mlE (e.map τ), (hU he).1, e.map τ, ⟨(hU he).2, e, rfl⟩, rfl⟩

end PositivityTheory.Rg.Sw.Glob.DenseP
