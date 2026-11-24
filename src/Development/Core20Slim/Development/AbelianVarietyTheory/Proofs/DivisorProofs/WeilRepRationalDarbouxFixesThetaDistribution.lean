module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaDistributionSumProductFunctionStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZeroStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumDoubledWeilFixedDiagonalStabilizerStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumDoubledWeilAntidiagonalInvariantStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryRationalEqDiagonalFixersProductStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.WeilThetaRat

theorem dbl_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    {κ : Type} [Fintype κ] (hκ : Fintype.card κ = a * b)
    (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ)
    (hd : ∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F,
      d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ))
    (hdd : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd) (χ : Chr F E) (hχ : IsHecke F E χ)
    (omd : UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ))
    (hS : IsSplitting (adeleClass F) ψ dd (actB (cA σ)) omd)
    (hR : SiegelRule (cA σ) (adeleClass F) ψ (-1) (incM F JA) (dbl (incM F JB)) dd χ (diagCols (Fin b)) omd)
    (g : UG (cA σ) (dbl (incM F JB))) (g₀ : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) E) (hg : ((g : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F g₀) :
    ∀ φ ∈ schA F (κ ⊕ κ), thetaSum F (omd g φ) = thetaSum F φ := by
  intro φ hφ
  obtain ⟨p, q, p', p₀, q₀, p₀', t, s, t', hp, hq, hp', ht, hs, ht', rfl⟩ :=
    GlobalTheory.T.doubledUnitary_rational_eq_diagonalFixers_product F E σ hσ b JB ε hJ hdet g g₀ hg
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  calc
    _ = thetaSum F (omd q (omd p' φ)) :=
      GlobalTheory.T.thetaSum_doubledWeil_fixed_diagonalStabilizer F E σ hσ ψ hψ a b JA JB κ hκ d hd dd hdd χ hχ omd hS hR p p₀ hp t ht (omd q (omd p' φ)) (hS.pres q _ (hS.pres p' _ hφ))
    _ = thetaSum F (omd p' φ) :=
      GlobalTheory.T.adelicThetaSum_doubledWeil_antidiagonal_invariant F E σ hσ ψ hψ a b JA JB κ hκ d hd dd hdd χ hχ omd hS hR q q₀ hq s hs (omd p' φ) (hS.pres p' _ hφ)
    _ = thetaSum F φ :=
      GlobalTheory.T.thetaSum_doubledWeil_fixed_diagonalStabilizer F E σ hσ ψ hψ a b JA JB κ hκ d hd dd hdd χ hχ omd hS hR p' p₀' hp' t' ht' φ hφ

theorem member_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    {κ : Type} [Fintype κ] (hκ : Fintype.card κ = a * b)
    (d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ)
    (hd : ∀ x : Matrix (Fin a) (Fin b) E, ∃ y z : κ → F,
      d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (χ : Chr F E) (hχ : IsHecke F E χ) (om : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ))
    (h : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d χ om)
    (γ : UG (cA σ) (incM F JB)) (γ₀ : Matrix (Fin b) (Fin b) E)
    (hγ : ((γ : GL (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b) (Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F γ₀) :
    ∀ Φ ∈ schA F κ, thetaSum F (om γ Φ) = thetaSum F Φ := by
  intro Φ hΦ
  obtain ⟨hom, dd, omd, hdd, ⟨-, hS, hR⟩, hres⟩ := h
  obtain ⟨gd, hgd⟩ := GlobalTheory.unitary_diag_one_mem_dbl (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (cA σ) (Fin b) (incM F JB) γ
  have hgd0 : ((gd : GL (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F (Matrix.fromBlocks γ₀ 0 0 1) := by
    rw [hgd, hγ]
    simp only [incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨φ₂, hφ₂, hθ⟩ := GlobalTheory.T.exists_adelicSchwartz_thetaDistributionSum_ne_zero F κ
  have hb := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ Φ hΦ φ₂ hφ₂
  have e1 := dbl_rat σ hσ ψ hψ JA JB ε hJ hdet hκ d hd dd hdd χ hχ omd hS.toIsSplitting hR gd _ hgd0 _ hb
  rw [hres γ gd hgd Φ hΦ φ₂ hφ₂, GlobalTheory.T.adelicThetaDistributionSum_productFunction F κ κ _ (hom.pres γ Φ hΦ) φ₂ hφ₂, GlobalTheory.T.adelicThetaDistributionSum_productFunction F κ κ Φ hΦ φ₂ hφ₂] at e1
  exact mul_right_cancel₀ hθ e1

theorem rat_mat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {γ : UA σ J} (hγ : γ ∈ ratU σ J) :
    ∃ γ₀ : Matrix (Fin n) (Fin n) E, ((γ.1 : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = incM F γ₀ := by
  obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.mp hγ
  refine ⟨(g₀ : Matrix (Fin n) (Fin n) E), ?_⟩
  rw [← hg₀]
  ext i j
  rfl

theorem thetaSum_om_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E), (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → (∀ i j, σ (JW j i) = -JW i j) → JW.det ≠ 0 → ∀ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW → ∀ om : UA σ JX × UA σ JW →* Module.End ℂ ((Fin n × Fin d → AF F) → ℂ), IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JW) co χX χW om → ∀ γ ∈ ratU σ JX, ∀ γ' ∈ ratU σ JW, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro F E _ _ _ _ _ σ hσ ψ hψ n d JX JW hX hXd hW hWd co hco χX χW hχX hχW om hom γ hγ γ' hγ' Φ hΦ
  obtain ⟨hB, ⟨d', hd', hA⟩, -⟩ := hom
  obtain ⟨g₀, hg₀⟩ := rat_mat hγ
  obtain ⟨g₀', hg₀'⟩ := rat_mat hγ'
  have eW : ∀ i j, σ (JW j i) = (((-1 : ℤˣ) : ℤ) : E) * JW i j := fun i j => by simp [hW i j]
  have eX : ∀ i j, σ (JX j i) = (((1 : ℤˣ) : ℤ) : E) * JX i j := fun i j => by simp [hX i j]
  have hco' : ∀ x : Matrix (Fin d) (Fin n) E, ∃ y z : Fin n × Fin d → F,
      d'.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun x => by
    have e : incM F x = (incM F xᵀ)ᵀ := by simp [incM, Matrix.transpose_map]
    rw [e, hd']
    exact hco xᵀ
  have hx : (γ, γ') = (γ, 1) * (1, γ') := by simp
  rw [hx, map_mul, Module.End.mul_apply]
  have e1 : om (γ, 1) = (om.comp (MonoidHom.inl _ _)) γ := rfl
  have e2 : om (1, γ') = (om.comp (MonoidHom.inr _ _)) γ' := rfl
  have hΦ' : om (1, γ') Φ ∈ schA F (Fin n × Fin d) := hB.1.pres γ' Φ hΦ
  rw [e1, member_rat σ hσ ψ hψ JW JX 1 eX hXd (by simp [Nat.mul_comm]) d' hco' χW hχW _ hA γ g₀ hg₀ _ hΦ', e2]
  exact member_rat σ hσ ψ hψ JX JW (-1) eW hWd (by simp) co hco χX hχX _ hB γ' g₀' hg₀' Φ hΦ

end GlobalTheory.WeilThetaRat
