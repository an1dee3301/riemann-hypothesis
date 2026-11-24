module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralLinear
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.DivMod.Bootstrap
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.List.Basic
public import Init.Data.Order.Lemmas
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Omega.Coeffs
public import Init.Omega.Constraint
public import Init.Omega.Int
public import Init.Omega.LinearCombo
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.RelClasses
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj.SymImageC

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

def refLev (p : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * p + 1) (fun i => 2 * (i.val + 1))

def refGroup (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c p : ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | GlobalTheory.RootEx.Radical.Uni (refLev p) g.val}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun ha hb => GlobalTheory.RootEx.Radical.Uni.mul ha hb
  inv_mem' := fun ha => GlobalTheory.RootEx.Radical.Uni.inv ha

theorem N_le_refGroup {p q : ℕ} (h₁ : p ≤ q) (h₂ : q ≤ p + 1) :
    GlobalTheory.RootEx.N k n c q ≤ refGroup k n c p := by
  intro g hg r s hrs
  refine (GlobalTheory.RootEx.Radical.mem_N_iff g).1 hg r s ?_
  rcases r with r | r <;> rcases s with s | s <;>
    simp only [refLev, Sum.elim_inl, Sum.elim_inr] at hrs <;>
    simp only [GlobalTheory.RootEx.lev, Sum.elim_inl, Sum.elim_inr] <;> omega

theorem symN_le_refGroup : symN k n c ≤ refGroup k n c ((c + 1) / 2) :=
  sup_le (N_le_refGroup le_rfl (by omega)) (N_le_refGroup (by omega) (by omega))

theorem toBlocks₁₁_of_mem_symN {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) : u.val.toBlocks₁₁ = 1 := by
  have h : GlobalTheory.RootEx.Radical.Uni (refLev ((c + 1) / 2)) u.val := symN_le_refGroup hu
  ext r s
  simp only [Matrix.toBlocks₁₁, Matrix.of_apply]
  rw [h _ _ (by simp [refLev])]
  simp [Matrix.one_apply]

theorem toBlocks₁₁_mul_embX {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) (g : GL n k) :
    (u * GlobalTheory.RootEx.embX c g).val.toBlocks₁₁ = g.val := by
  have h := toBlocks₁₁_of_mem_symN hu
  rw [Units.val_mul, GlobalTheory.RootEx.Radical.embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks u.val]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, h]
  simp

theorem toBlocks₁₁_inv_mul_embX {u : GL (n ⊕ Fin c) k} (hu : u ∈ symN k n c) (g : GL n k) :
    ((u * GlobalTheory.RootEx.embX c g)⁻¹).val.toBlocks₁₁ = (g⁻¹).val := by
  have h := toBlocks₁₁_of_mem_symN (inv_mem hu)
  rw [_root_.mul_inv_rev, ← map_inv, Units.val_mul, GlobalTheory.RootEx.Radical.embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (u⁻¹).val]
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁, h]
  simp

end GlobalTheory.FunObj.SymImageC


open GlobalTheory.FunObj.SymImageC in
theorem GlobalTheory.FunObj.SymImageC.symPr_open_bounded {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (C : Subgroup (GL (n ⊕ Fin c) k)) (hC : IsOpen (C : Set (GL (n ⊕ Fin c) k)))
    (hb : ∃ A : Set (GL (n ⊕ Fin c) k), IsCompact A ∧ (C : Set (GL (n ⊕ Fin c) k)) ⊆ A) :
    IsOpen (symPr C : Set (GL n k)) ∧ ∃ A : Set (GL n k), IsCompact A ∧ (symPr C : Set (GL n k)) ⊆ A := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  constructor
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    have ho := hC.preimage (GlobalTheory.RootEx.QuotLinear.continuous_embX (k := k) (n := n) (c := c))
    refine Filter.mem_of_superset (ho.mem_nhds (by simp [one_mem])) fun g hg => ?_
    exact ⟨1, one_mem _, by simpa using hg⟩
  · obtain ⟨A, hA, hCA⟩ := hb
    let φ : GL (n ⊕ Fin c) k → Matrix n n k × (Matrix n n k)ᵐᵒᵖ :=
      fun g => (g.val.toBlocks₁₁, MulOpposite.op (g⁻¹).val.toBlocks₁₁)
    have hbl : Continuous fun M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k => M.toBlocks₁₁ :=
      continuous_matrix fun i j => continuous_id.matrix_elem _ _
    have hφ : Continuous φ :=
      (hbl.comp Units.continuous_val).prodMk
        (MulOpposite.continuous_op.comp (hbl.comp Units.continuous_coe_inv))
    refine ⟨_, (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage (hA.image hφ),
      ?_⟩
    rintro g ⟨u, hu, h⟩
    refine ⟨_, hCA h, ?_⟩
    simp only [φ]
    rw [toBlocks₁₁_mul_embX hu, toBlocks₁₁_inv_mul_embX hu]
    rfl
