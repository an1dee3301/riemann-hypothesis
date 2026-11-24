module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.List.Basic
public import Init.Data.List.OfFn
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.Order.Notation
public import Mathlib.Order.TypeTags
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.Grow GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.PointAtPlaceHom

namespace GlobalTheory.Size

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem adAt_mem_lieAt (hθ : IsInfFam θ) (k : GA D V) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : adAt θ k τ X ∈ lieAt V τ := by

  have hU : Matrix.conjTranspose (infMat D.sp.cm.sig V.gram (θ τ) k) * gramAt D V τ *
      infMat D.sp.cm.sig V.gram (θ τ) k = gramAt D V τ :=
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V k τ
  exact skew_conj hU (GlobalTheory.Mem.AutSpace.infMat_mul_inv (θ := θ) (V := V) (τ := τ) (g := k)) hX

private theorem infMat_eq_one_of_mem_GfC {f : GA D V} (hf : f ∈ GfC V) (τ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (θ τ) f = 1 := by

  have h1 : infHom V f = 1 := hf
  have h2 := congrArg (fun u => (u.val).map (θ τ)) h1
  simp only [Units.val_one] at h2
  rw [Matrix.map_one (θ τ) (map_zero (θ τ)) (map_one (θ τ))] at h2
  exact h2

private theorem adAt_mul_of_mem_GfC (a : GA D V) {f : GA D V} (hf : f ∈ GfC V) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) : adAt θ (a * f) τ X = adAt θ a τ X := by

  unfold adAt
  rw [mul_inv_rev, GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.PointAtPlaceHom.infMat_mul, infMat_eq_one_of_mem_GfC hf τ,
    infMat_eq_one_of_mem_GfC (inv_mem hf) τ, one_mul, mul_one]

theorem oneP_mul_adelic (hθ : IsInfFam θ) (k : GA D V) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (t : ℝ) : oneP θ V τ X t * k = k * oneP θ V τ (adAt θ k τ X) t := by

  obtain ⟨a, ha, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 k
  have hreal : IsRealPt θ a := ⟨ha, fun σ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a σ⟩
  have hinf : oneP θ V τ (adAt θ a τ X) t ∈ GinfC V := atTau_mem V τ _
  rw [adAt_mul_of_mem_GfC a hf, ← mul_assoc, oneP_mul hθ hreal hX t, mul_assoc, mul_assoc,
    comm_of_mem V hinf hf]

theorem Rder_rTr_adelic (hθ : IsInfFam θ) (k : GA D V) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (φ : GA D V → ℂ) :
    Rder θ V τ X (rTr V k φ) = rTr V k (Rder θ V τ (adAt θ k τ X) φ) := by

  funext g
  show deriv (fun t : ℝ => φ (g * oneP θ V τ X t * k)) 0 = deriv (fun t : ℝ => φ (g * k * oneP θ V τ (adAt θ k τ X) t)) 0
  congr 1
  funext t
  rw [mul_assoc, oneP_mul_adelic hθ k hX t, ← mul_assoc]

theorem rWord_rTr_adelic (hθ : IsInfFam θ) (k : GA D V) (φ : GA D V → ℂ)
    {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)} (hl : IsLieWord V l) :
    rWord θ V l (rTr V k φ) = rTr V k (rWord θ V (l.map fun p => (p.1, adAt θ k p.1 p.2)) φ) := by

  induction l with
  | nil => simp only [rWord, wordAct, List.foldr_nil, List.map_nil]
  | cons p l ih =>
    have hp : p.2 ∈ lieAt V p.1 := hl p List.mem_cons_self
    have hl' : IsLieWord V l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have ih' := ih hl'
    simp only [rWord, wordAct, List.foldr_cons, List.map_cons] at ih' ⊢
    rw [ih', Rder_rTr_adelic hθ k hp]

theorem rTr_mem_smFun (hθ : IsInfFam θ) (k : GA D V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) :
    rTr V k φ ∈ SmFun θ V := by

  intro n τs Xs hXs g
  have key := hφ n τs (fun i => adAt θ k (τs i) (Xs i)) (fun i => adAt_mem_lieAt hθ k (hXs i)) (g * k)
  convert key using 1
  funext t
  show φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod * k) =
    φ (g * k * (List.ofFn fun i => oneP θ V (τs i) (adAt θ k (τs i) (Xs i)) (t i)).prod)
  rw [mul_assoc, prod_mul_eq k n (fun i => oneP θ V (τs i) (Xs i) (t i))
    (fun i => oneP θ V (τs i) (adAt θ k (τs i) (Xs i)) (t i)) (fun i => oneP_mul_adelic hθ k (hXs i) (t i)),
    ← mul_assoc]

private theorem rapidDecSm_rTr_of_mem_GinfC (hθ : IsInfFam θ) {a : GA D V} (ha : a ∈ GinfC V) {φ : GA D V → ℂ}
    (h : RapidDecSm θ V φ) : RapidDecSm θ V (Formalism.L2.Theta.rTr V a φ) := by

  have hR := h.rapidDec.mul_right a
  refine ⟨⟨hR.1, ?_, hR.2.1⟩, rTr_mem_smFun hθ a h.smooth, fun l hl => ?_⟩
  · obtain ⟨U, hU, hUφ⟩ := h.level
    refine ⟨U, hU, fun u hu huf g => ?_⟩
    show φ (g * u * a) = φ (g * a)
    rw [mul_assoc, ← comm_of_mem V ha huf, ← mul_assoc, hUφ u hu huf]
  · rw [rWord_rTr_adelic hθ a φ hl]
    refine (h.decay _ fun p hp => ?_).mul_right a
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact adAt_mem_lieAt hθ a (hl q hq)

theorem RapidDecSm.rTr (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : RapidDecSm θ V φ) (k : GA D V) :
    RapidDecSm θ V (Formalism.L2.Theta.rTr V k φ) := by

  obtain ⟨a, ha, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 k
  have e : Formalism.L2.Theta.rTr V (a * f) φ = Formalism.L2.Theta.rTr V a (Formalism.L2.Theta.rTr V f φ) := by
    funext g
    simp only [Formalism.L2.Theta.rTr, mul_assoc]
  rw [e]
  exact rapidDecSm_rTr_of_mem_GinfC hθ ha (h.rTr_fin hf)

end GlobalTheory.Size

end
