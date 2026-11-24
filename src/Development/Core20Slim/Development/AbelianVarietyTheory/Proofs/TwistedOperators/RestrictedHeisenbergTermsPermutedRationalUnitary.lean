module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisOApplyZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Function
public import Init.Data.Int.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistEquiRat

variable {D : D7}

theorem integral_mul_left {m n : ℕ} (μ : Measure (Mx D m n)) (𝓨 : Set (Mx D m n))
    (h : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) μ 𝓨) (P Q : Mx D m m) (hP : P ∈ GlobalTheory.MixModel.ratMx D m m)
    (hQ : Q ∈ GlobalTheory.MixModel.ratMx D m m) (hPQ : P * Q = 1) (hQP : Q * P = 1) (φ : Mx D m n → ℂ)
    (hφ : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∀ a, φ (γ + a) = φ a) :
    ∫ a in 𝓨, φ (P * a) ∂μ = ∫ a in 𝓨, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  let eA : Mx D m n ≃+ Mx D m n :=
    { toFun := fun a => P * a
      invFun := fun a => Q * a
      left_inv := fun a => by show Q * (P * a) = a; rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
      right_inv := fun a => by show P * (Q * a) = a; rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
      map_add' := fun a b => Matrix.mul_add P a b }
  have hc : Continuous (fun a : Mx D m n => P * a) := continuous_const.matrix_mul continuous_id
  have hc' : Continuous (fun a : Mx D m n => Q * a) := continuous_const.matrix_mul continuous_id
  let eH : Mx D m n ≃ₜ Mx D m n := ⟨eA.toEquiv, hc, hc'⟩
  let eM : Mx D m n ≃ᵐ Mx D m n := eH.toMeasurableEquiv
  haveI := h.1
  have hHaar : (μ.map eM).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ eA hc hc'
  have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (μ.map eM) μ := MeasurePreserving.symm eM hmp
  let eG : GlobalTheory.MixModel.ratMx D m n → GlobalTheory.MixModel.ratMx D m n :=
    fun g => ⟨P * (g : Mx D m n), GlobalTheory.MixModel.ratMx_mul hP g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨Q * (g : Mx D m n), GlobalTheory.MixModel.ratMx_mul hQ g.2⟩, ?_⟩⟩
    · have e := congrArg (fun x : GlobalTheory.MixModel.ratMx D m n => Q * (x : Mx D m n)) hg
      simp only [eG, ← Matrix.mul_assoc, hQP, Matrix.one_mul] at e
      exact Subtype.ext e
    · apply Subtype.ext
      show P * (Q * (g : Mx D m n)) = g
      rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hF : IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D m n) (eM.symm ⁻¹' 𝓨) (μ.map eM) := by
    refine h.2.1.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
    show Q * (P * (g : Mx D m n) + x) = (g : Mx D m n) + Q * x
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hpre : eM ⁻¹' (eM.symm ⁻¹' 𝓨) = 𝓨 := by
    ext a; simp
  have hvol : (μ.map eM) (eM.symm ⁻¹' 𝓨) = 1 := by
    rw [MeasurableEquiv.map_apply, hpre]; exact h.2.2
  have e1 := hmp.setIntegral_preimage_emb eM.measurableEmbedding φ (eM.symm ⁻¹' 𝓨)
  rw [hpre] at e1
  exact e1.trans (GlobalTheory.MixModel.covolOne_integral_eq h ⟨hHaar, hF, hvol⟩ φ hφ)

theorem symplOH_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C)
    (q₀ : Matrix (Fin W.rank) (Fin r) D.host.E) (a : Mx D W.rank r) :
    symplOH V W (isoPart V W C (q₀.map (incA D))) (isoPart V W C a) = 0 := by
  set X : Mx D r V.rank := (adj D C * V.gram).map (incA D) with hXdef
  have hM : (adj D C * V.gram)ᴴ = V.gram * C := by
    rw [Matrix.conjTranspose_mul, GlobalTheory.MixModel.gram_conjTranspose]
    show V.gram * (Cᴴ)ᴴ = V.gram * C
    rw [Matrix.conjTranspose_conjTranspose]
  have hX0 : X * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X = 0 := by
    have e : GlobalTheory.MixModel.adj X = GlobalTheory.MixModel.rat (V.gram * C) := by
      rw [hXdef, ← hM]; rfl
    rw [e, hXdef]
    show GlobalTheory.MixModel.rat (adj D C * V.gram) * GlobalTheory.MixModel.rat V.gram⁻¹ * GlobalTheory.MixModel.rat (V.gram * C) = 0
    rw [← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (V.gram * C) = adj D C * V.gram * C := by
      rw [Matrix.mul_assoc (adj D C * V.gram), ← Matrix.mul_assoc V.gram⁻¹,
        Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
    rw [this]
    exact (congrArg GlobalTheory.MixModel.rat hC.2.2).trans GlobalTheory.MixModel.rat_zero
  rw [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace]
  have e2 : isoPart V W C (q₀.map (incA D)) = q₀.map (incA D) * X := rfl
  have e3 : isoPart V W C a = a * X := rfl
  rw [e2, e3, GlobalTheory.MixModel.adj_mul]
  have e4 : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.adj X * GlobalTheory.MixModel.adj a * (GlobalTheory.MixModel.gA W * (q₀.map (incA D) * X)))
      = (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X * GlobalTheory.MixModel.adj a * GlobalTheory.MixModel.gA W * q₀.map (incA D)) * X := by
    simp only [Matrix.mul_assoc]
  rw [e4, Matrix.trace_mul_comm]
  have e5 : X * (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X * GlobalTheory.MixModel.adj a * GlobalTheory.MixModel.gA W * q₀.map (incA D))
      = (X * GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.adj X) * (GlobalTheory.MixModel.adj a * GlobalTheory.MixModel.gA W * q₀.map (incA D)) := by
    simp only [Matrix.mul_assoc]
  rw [e5, hX0, Matrix.zero_mul, Matrix.trace_zero, map_zero]

theorem isoPart_add (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (y z : Mx D W.rank r) :
    isoPart V W C (y + z) = isoPart V W C y + isoPart V W C z := by
  unfold isoPart; exact Matrix.add_mul _ _ _

theorem ratW_eq_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (q₀ : Matrix (Fin W.rank) (Fin r) D.host.E) :
    ratW W V (q₀ * (adj D C * V.gram)) = isoPart V W C (q₀.map (incA D)) := by
  unfold isoPart ratW; exact Matrix.map_mul

end GlobalTheory.TwistEquiRat

namespace GlobalTheory.TwistEquiRat

theorem res_heisO_rat_equi : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (γ : GA D W) (γ₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), γ ∈ GQ W → Formalism.L2.Theta.mt W γ = γ₀.map (incA D) → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map (γ₀ * y) (incA D))) (ω (1, γ) f)) 0 = res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) f) 0 := by
  intro D V V' W r C C' B hs _ _ _ ψ χS χT ω hω μ 𝓨 hμ γ γ₀ hγ hγ₀ y f hf
  have hstd := hω.std
  set w₀ := isoPart V W C' (Matrix.map y (incA D)) with hw₀
  have hact : ∀ x : WO V W, actO V W 1 γ x = Formalism.L2.Theta.mt W γ * x := by
    intro x
    rw [GlobalTheory.MixModel.actO_eq, inv_one, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have e1 : isoPart V W C' (Matrix.map (γ₀ * y) (incA D)) = actO V W 1 γ w₀ := by
    rw [hact, hw₀]
    show Matrix.map (γ₀ * y) (incA D) * (((adj D C' * V.gram).map (incA D)) : Mx D r V.rank) = Formalism.L2.Theta.mt W γ * (Matrix.map y (incA D) * (((adj D C' * V.gram).map (incA D)) : Mx D r V.rank))
    rw [Matrix.map_mul, ← hγ₀, Matrix.mul_assoc]
  have e2 : heisO ψ V W (isoPart V W C' (Matrix.map (γ₀ * y) (incA D))) (ω (1, γ) f) =
      ω (1, γ) (heisO ψ V W w₀ f) := by
    rw [e1]; exact (hω.om_heis 1 γ w₀ f hf).symm
  rw [e2]
  set G := heisO ψ V W w₀ f with hGdef
  have hG : IsThetaFunO ψ V W G := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hstd V W).1 w₀ f hf
  have hrat := GlobalTheory.WeilRat.om_rat_actO D ψ hstd V W χS χT ω hω 1 (one_mem _) γ hγ G hG
  have hQP : Formalism.L2.Theta.mt W γ * Formalism.L2.Theta.mt W γ⁻¹ = 1 := GlobalTheory.MixModel.mt_mul_inv W γ
  have hPQ : Formalism.L2.Theta.mt W γ⁻¹ * Formalism.L2.Theta.mt W γ = 1 := GlobalTheory.MixModel.mt_inv_mul W γ
  have hmid : midPart V V' W B 0 = 0 := by
    show HMul.hMul (0 : Matrix (Fin W.rank) (Fin V'.rank) (AE D)) _ = 0
    exact Matrix.zero_mul _
  have hpt : ∀ a, ω (1, γ) G (isoPart V W C a + midPart V V' W B 0) =
      G (isoPart V W C (Formalism.L2.Theta.mt W γ⁻¹ * a) + midPart V V' W B 0) := by
    intro a
    rw [hmid, add_zero, add_zero, ← hrat, hact]
    refine congrArg (ω (1, γ) G) ?_
    show a * (((adj D C * V.gram).map (incA D)) : Mx D r V.rank) = Formalism.L2.Theta.mt W γ * (Formalism.L2.Theta.mt W γ⁻¹ * a * (((adj D C * V.gram).map (incA D)) : Mx D r V.rank))
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  show ∫ a in 𝓨, ω (1, γ) G (isoPart V W C a + midPart V V' W B 0) ∂μ =
    ∫ a in 𝓨, G (isoPart V W C a + midPart V V' W B 0) ∂μ
  simp only [hpt]
  have hper : ∀ q ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ a,
      G (isoPart V W C (q + a) + midPart V V' W B 0) = G (isoPart V W C a + midPart V V' W B 0) := by
    intro q hq a
    obtain ⟨q₀, rfl⟩ := hq
    have e3 : (incA D).toAddMonoidHom.mapMatrix q₀ = q₀.map (incA D) := rfl
    rw [hmid, add_zero, add_zero, e3, isoPart_add, ← ratW_eq_isoPart, hG.quasi, ratW_eq_isoPart, symplOH_isoPart V W C hs.frame, neg_zero, AddChar.map_zero_eq_one,
      one_mul]
  exact integral_mul_left μ 𝓨 hμ _ _ ((GlobalTheory.MixModel.mem_GQ_iff W γ⁻¹).1 (inv_mem hγ))
    ((GlobalTheory.MixModel.mem_GQ_iff W γ).1 hγ) hPQ hQP (fun a => G (isoPart V W C a + midPart V V' W B 0)) hper

end GlobalTheory.TwistEquiRat
