module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReprMemOfCoeff
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingPairingMemCoefficientField
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.UniqueProds.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Logic.Function.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open Formalism.L2.DIV MvPolynomial

namespace GlobalTheory.RowFun

theorem coeff_mem_of_mul_eq {s : Type} (K' : Subfield ℂ) (f P Q : MvPolynomial s ℂ) (hP : P ≠ 0)
    (hPK : ∀ m, AddMonoidAlgebra.coeff P m ∈ K') (hQ : ∀ m, AddMonoidAlgebra.coeff Q m ∈ K') (h : f * P = Q) :
    ∀ m, AddMonoidAlgebra.coeff f m ∈ K' := by
  classical
  obtain ⟨φ, hφ1, hφ2⟩ := GlobalTheory.RowRat.exists_proj K'
  let g : MvPolynomial s ℂ := ∑ m ∈ f.support, monomial m (φ (AddMonoidAlgebra.coeff f m))
  have hg : ∀ m, AddMonoidAlgebra.coeff g m = φ (AddMonoidAlgebra.coeff f m) := by
    intro m
    simp only [g, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with hm
    · rfl
    · rw [notMem_support_iff.mp hm, map_zero]
  have key : g * P = f * P := by
    ext m
    have hfix : AddMonoidAlgebra.coeff (f * P) m = φ (AddMonoidAlgebra.coeff (f * P) m) := by
      rw [h]; exact (hφ1 ⟨_, hQ m⟩).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hfix, coeff_mul, coeff_mul, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hg]
    have hs := φ.map_smul (⟨AddMonoidAlgebra.coeff P x.2, hPK _⟩ : K') (AddMonoidAlgebra.coeff f x.1)
    rw [Subfield.smul_def, Subfield.smul_def, smul_eq_mul, smul_eq_mul] at hs
    rw [mul_comm, ← hs, mul_comm]
  have hgf : g = f := mul_right_cancel₀ hP key
  intro m
  rw [← hgf, hg]
  exact hφ2 _

theorem coeff_funOf_mem_range {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → Formalism.BasicNotions.DomWeight n) {L : Type}
    [Field L] (κ : L →+* ℂ) (hR : GlobalTheory.FunObj.ReadOK σ) (F : VV ℂ σ)
    (hF : ∀ m, AddMonoidAlgebra.coeff F.1 m ∈ Set.range κ) :
    ∀ m, AddMonoidAlgebra.coeff (GlobalTheory.FunObj.funOf σ F).1 m ∈ Set.range κ := by
  classical
  have hf := hR.1 F
  unfold GlobalTheory.FunObj.IsFunForm at hf
  let G : MvPolynomial (ι × Fin n × Fin n) L :=
    ∑ m ∈ (F.1 : MvPolynomial (ι × Fin n × Fin n) ℂ).support,
      monomial m (Function.invFun κ (AddMonoidAlgebra.coeff F.1 m))
  have hG : MvPolynomial.map κ G = F.1 := by
    ext m
    rw [coeff_map]
    simp only [G, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with hm
    · exact Function.invFun_eq (hF m)
    · simp [notMem_support_iff.mp hm]
  have hmem : ∀ (p : MvPolynomial (ι × Fin n × Fin n) L) m,
      AddMonoidAlgebra.coeff (MvPolynomial.map κ p) m ∈ κ.fieldRange := fun p m => by
    rw [coeff_map]; exact RingHom.mem_fieldRange_self κ _
  have hmem_eq₁ : MvPolynomial.map κ (∏ τ, Formalism.L2.Ker.frDet L n τ ^ ∑ a, (σ τ).natW a)
      = ∏ τ, Formalism.L2.Ker.frDet ℂ n τ ^ ∑ a, (σ τ).natW a := by
    simp only [map_prod, map_pow, GlobalTheory.BrRat.map_frDet]
  have hmem_eq₂ : MvPolynomial.map κ (GlobalTheory.FunObj.dualSubst L ι n G *
      ∏ τ, Formalism.L2.Ker.frDet L n τ ^ (-(σ τ).dual.detShift - (σ τ).detShift).toNat)
      = GlobalTheory.FunObj.dualSubst ℂ ι n F.1 *
      ∏ τ, Formalism.L2.Ker.frDet ℂ n τ ^ (-(σ τ).dual.detShift - (σ τ).detShift).toNat := by
    simp only [map_mul, map_prod, map_pow, GlobalTheory.BrRat.map_frDet, GlobalTheory.BrRat.map_dualSubst, hG]
  intro m
  have := coeff_mem_of_mul_eq κ.fieldRange _ _ _
    (Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ (GlobalTheory.FunObj.funFrDet_ne_zero τ))
    (fun m => by
      rw [← hmem_eq₁]; exact hmem _ m)
    (fun m => by
      rw [← hmem_eq₂]; exact hmem _ m) hf m
  exact RingHom.mem_fieldRange.mp this

end GlobalTheory.RowFun
