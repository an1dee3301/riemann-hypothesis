module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
public import Init.Data.Zero
public import Init.Prelude
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.CenAct

variable {D : D7}

abbrev finf (D : D7) : AE D →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem mem_GfC_iff (V : HSp D) (g : GA D V) : g ∈ GfC V ↔ (Formalism.L2.Theta.mt V g).map (finf D) = 1 := by
  show infHom V g = 1 ↔ _
  rw [Units.ext_iff]
  rfl

theorem map_sand {k n : ℕ} (x : Mx D k n) (m : Mx D n n)
    (y : Mx D n k) (hm : m.map (finf D) = 1) :
    (x * m * y).map (finf D) = (x * y).map (finf D) := by
  have e1 : (x * m * y).map (finf D) = x.map (finf D) * m.map (finf D) * y.map (finf D) := by
    rw [Matrix.map_mul (f := finf D), Matrix.map_mul (f := finf D)]
  have e2 : (x * y).map (finf D) = x.map (finf D) * y.map (finf D) := Matrix.map_mul (f := finf D)
  rw [e1, e2, hm, Matrix.mul_one]

theorem orth_emb_mem_GfC {S A B : HSp D} (o : OrthDec S A B) {a : GA D A} (ha : a ∈ GfC A) :
    o.emb (a, 1) ∈ GfC S := by
  rw [mem_GfC_iff] at ha ⊢
  rw [OrthDec.mt_emb, Matrix.map_add _ (map_add (finf D)), map_sand _ _ _ ha, GlobalTheory.MixModel.mt_one, Matrix.mul_one, ← Matrix.map_add _ (map_add (finf D)),
    o.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem witt_embedding_mem_finite_unitary_points {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {g : GA D S₀} (hg : g ∈ GfC S₀) :
    d.emb0 g ∈ GfC S := by
  rw [mem_GfC_iff] at hg ⊢
  rw [HypDec.unitaryMatrix_wittCoreEmbedding, Matrix.map_add _ (map_add (finf D)), Matrix.map_add _ (map_add (finf D)), map_sand _ _ _ hg, ← Matrix.map_add _ (map_add (finf D)), ← Matrix.map_add _ (map_add (finf D)),
    d.sum_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem embA_mem_GfC {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {a : GA D A}
    (ha : a ∈ GfC A) : embA d o a ∈ GfC S := by
  rw [embA_apply]
  exact witt_embedding_mem_finite_unitary_points d (orth_emb_mem_GfC o ha)



end GlobalTheory.Core.Mi.CenAct

namespace GlobalTheory.Core.Mi.CenAct

variable {D : D7} {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D}






end GlobalTheory.Core.Mi.CenAct


end
