module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromColsMemLatDbl
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Sum.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

namespace GlobalTheory.DblFill

theorem symp_dbl {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (x y : Matrix α (β ⊕ β) E) :
    symp c ξ JA (dbl JB) x y = symp c ξ JA JB x.toCols₁ y.toCols₁ - symp c ξ JA JB x.toCols₂ y.toCols₂ := by
  unfold symp hTens
  rw [← map_sub, ← mul_sub]
  congr 2
  simp only [Fintype.sum_sum_type, dbl, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.toCols₁_apply, Matrix.toCols₂_apply, Matrix.zero_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem symp_zero_right {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x : Matrix α β E) :
    symp c ξ JA JB x 0 = 0 := by
  simp [symp, hTens]

end GlobalTheory.DblFill

namespace GlobalTheory.DblFill

theorem at_toCols₁ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    {v : Pl (F := F)} {z : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)} (hz : At (evFin F v) z) : At (evFin F v) z.toCols₁ := by
  intro u hu
  have := hz u hu
  ext i j
  simpa using congrFun (congrFun this i) (Sum.inl j)

theorem at_toCols₂ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    {v : Pl (F := F)} {z : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)} (hz : At (evFin F v) z) : At (evFin F v) z.toCols₂ := by
  intro u hu
  have := hz u hu
  ext i j
  simpa using congrFun (congrFun this i) (Sum.inr j)

theorem latDbl_fill : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M.co dd →
    ∀ η : (Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v,
      (∀ b, ((0 : (Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v), b) ∈ (latDbl G.V G.W v).map (GlobalTheory.LatVac.locCo dd v) →
        GlobalTheory.LatVac.psiAt B.ψ v (η ⬝ᵥ b) = 1) →
      ∃ y, (η, y) ∈ (latDbl G.V G.W v).map (GlobalTheory.LatVac.locCo dd v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hvw dd hdd η hη
  have hunr : PsiUnr B.ψ v := (hT.base.inert v w hvw).2.2
  have hsd := GlobalTheory.InertSelfDual.latAtV_selfDual F E σ B a a' G X om om' hT v w hvw

  have hglob : ∀ z : Matrix (Fin a) (Fin (a + a') ⊕ Fin (a + a')) (AE F E), At (evFin F v) z →
      (z ∈ latDbl G.V G.W v ↔ ∀ γ ∈ latDbl G.V G.W v,
        B.ψ (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) z γ) = 1) := by
    intro z hz
    have h1 := hsd _ (at_toCols₁ hz)
    have h2 := hsd _ (at_toCols₂ hz)
    unfold cA incM at h1 h2
    constructor
    · intro hzm γ hγ
      rw [symp_dbl, AddChar.map_sub_eq_div, (h1.1 hzm.1) _ hγ.1, (h2.1 hzm.2) _ hγ.2, div_one]
    · intro hψ
      refine ⟨h1.2 fun γ₁ hγ₁ => ?_, h2.2 fun γ₂ hγ₂ => ?_⟩
      · have := hψ (Matrix.fromCols γ₁ 0) (fromCols_mem_latDbl _ _ _ hγ₁ (zero_mem _))
        rwa [symp_dbl, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols, symp_zero_right, sub_zero] at this
      · have := hψ (Matrix.fromCols 0 γ₂) (fromCols_mem_latDbl _ _ _ (zero_mem _) hγ₂)
        rw [symp_dbl, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols, symp_zero_right, zero_sub,
          AddChar.map_neg_eq_inv] at this
        exact inv_eq_one.1 this
  have hloc := GlobalTheory.LatVac.DualLoc.map_selfDual v dd B.ψ (latDbl G.V G.W v)
    (fun γ hγ => at_of_mem_latDbl _ _ _ hγ) hglob
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V G.W v G.M.co hT.geo.hV.lat.toIsLattice hT.geo.hW.lat.toIsLattice
  have hbd : ∀ l ∈ (latDbl G.V G.W v).map (GlobalTheory.LatVac.locCo dd v), ∀ i,
      c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F := by
    rintro l ⟨z, hz, rfl⟩ i
    have hzc : z = Matrix.fromCols z.toCols₁ z.toCols₂ := (Matrix.fromCols_toCols z).symm
    have he := hdd z.toCols₁ z.toCols₂
    rw [← hzc] at he
    have k1 := hc _ hz.1
    have k2 := hc _ hz.2
    rcases i with k | k
    · simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, he, Sum.elim_inl]
      exact k1 k
    · simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, he, Sum.elim_inr, Pi.neg_apply, map_neg,
        mul_neg]
      exact ⟨(k2 k).1, neg_mem (k2 k).2⟩
  exact GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt B.ψ v) _ c hc0 hunr hloc hbd η hη

end GlobalTheory.DblFill
