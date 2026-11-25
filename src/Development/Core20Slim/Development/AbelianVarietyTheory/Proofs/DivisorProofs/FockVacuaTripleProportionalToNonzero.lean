module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatibleStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.GaussLine

theorem incM_map_piInf' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n m : Type}
    (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ) = J.map τ.1 := by
  ext i j
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf, compInf, inclR, infEmb_tmul]

theorem Jm_transpose'' (p q : ℕ) : (Jm p q)ᵀ = Jm p q := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_transpose]

theorem gauss_eq_smul : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W),
    IsTriple B Γ X om om' → ∀ f₀, f₀ ≠ 0 → Γ.M.IsGauss B.ψ B.emb f₀ → ∀ g, Γ.M.IsGauss B.ψ B.emb g → ∃ c : ℂ, g = c • f₀ := by
  intro F E _ _ _ _ _ σ a a' B Γ X om om' h f₀ hf₀ hG₀ g hg
  obtain ⟨hb, hgeo, -, -, -⟩ := h
  choose A hA hAθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hgeo.hV.sig w) (hgeo.hV.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hgeo.hW.sig w) (hgeo.hW.cartan w)
  have hA1 : ∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J).map
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf', one_smul]; exact hA w
  have hC1 : ∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.W.J).map
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf']; exact hC w
  have fr : GlobalTheory.RealLift.Framed B.emb (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.W.J) 1 Complex.I A C :=
    ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ Γ.M.co 1 Complex.I A C hb.cm hb.std fr
  have hz0 : ∀ (u : Matrix (Fin a) (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (t : ℝ),
      Γ.M.co.rho B.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F t • u) 0 = 0 := by
    intro u t; funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
  have toD : ∀ u (f f₁ : SInf F (Fin a × Fin (a + a'))),
      GlobalTheory.RealLift.SD (fun t => Γ.M.co.rho B.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F t • u)) f f₁ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (Γ.M.heisLine B.ψ u) f f₁ :=
    fun u f f₁ h => (GlobalTheory.T.archActionReadings_compatible F (Fin a × Fin (a + a')) f f₁ f₁).1 _ (hz0 u) h
  have tw : ∀ w (c : Matrix (Ix (a - Γ.p) Γ.p) (Ix (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) ℂ) (e : ℂ),
      A w * (e • (Jm (a - Γ.p) Γ.p * c * Jm (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q))) * (C w)ᵀ = e • (Γ.V.θ w * (A w * c * (C w)ᵀ) * (Γ.W.θ w)ᵀ) := by
    intro w c e
    have h2 : (C w)ᵀ * (Γ.W.θ w)ᵀ = Jm (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) * (C w)ᵀ := by
      rw [← Matrix.transpose_mul, hCθ w, Matrix.transpose_mul, Jm_transpose'']
    calc A w * (e • (Jm (a - Γ.p) Γ.p * c * Jm (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q))) * (C w)ᵀ = e • ((A w * Jm (a - Γ.p) Γ.p) * c * (Jm (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) * (C w)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [← hAθ w, ← h2]; simp only [Matrix.mul_assoc]
  have line : ∀ f, Γ.M.IsGauss B.ψ B.emb f →
      ∃ z : ℂ, f = z • Φ (PiTensorProduct.tprod ℂ fun _ => 1) := by
    rintro f ⟨ε, hε⟩
    exact GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ Γ.M.co 1 Complex.I A C Φ hb.cm hb.std fr hΦ f ε
      (fun u u' hu hu' c hc hc' f1 f1' hf hf' =>
        hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w]) f1 f1' (toD _ _ _ hf) (toD _ _ _ hf'))
  obtain ⟨z, hz⟩ := line f₀ hG₀
  obtain ⟨z', hz'⟩ := line g hg
  have hz0' : z ≠ 0 := by
    rintro rfl
    exact hf₀ (by rw [hz, zero_smul])
  exact ⟨z' / z, by rw [hz', hz, smul_smul, div_mul_cancel₀ _ hz0']⟩

end GlobalTheory.GaussLine

end
