module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixMulVecMemAdeleIdealSupportedOnPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
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
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.FinPl.OrbitCoset

variable {D : D7}

theorem mem_congGrp_iff' (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ (mt V g).map (Ideal.Quotient.mk I) = 1 := by
  unfold congGrp
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  rfl

theorem matrixTransform_wittCoreEmbedding {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (h : GA D S₀) :
    mt S (d.emb0 h) = d.jX ⬝ d.pX + d.j0 ⬝ mt S₀ h ⬝ d.p0 + d.jY ⬝ d.pY := by
  conv_lhs => rw [← Matrix.mul_one (mt S (d.emb0 h)), ← d.sum_eq_one]
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclY]

theorem wittCoreEmbedding_mem_supportedSubgroup {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (P : Pl D → Prop) {h : GA D S₀}
    (hh : h ∈ grpAt S₀ P) : d.emb0 h ∈ grpAt S P := by
  rw [grpAt, mem_congGrp_iff'] at hh ⊢
  have hadd : ∀ A B : Matrix (Fin S.rank) (Fin S.rank) (AE D), (A + B).map (Ideal.Quotient.mk (idAt D P)) =
      A.map (Ideal.Quotient.mk (idAt D P)) + B.map (Ideal.Quotient.mk (idAt D P)) :=
    fun A B => Matrix.map_add _ (Ideal.Quotient.mk (idAt D P)).map_add A B
  have key : (mt S (d.emb0 h)).map (Ideal.Quotient.mk (idAt D P)) =
      (d.jX ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ d.pY).map (Ideal.Quotient.mk (idAt D P)) := by
    rw [matrixTransform_wittCoreEmbedding]; simp only [hadd, Matrix.map_mul, hh, Matrix.mul_one]
  rw [key, d.sum_eq_one]
  exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem emb_mem_grpAt' {S A B : HSp D} (o : OrthDec S A B) {P : Pl D → Prop} {a : GA D A} (ha : a ∈ grpAt A P) :
    o.emb (a, 1) ∈ grpAt S P := by
  rw [grpAt, mem_congGrp_iff'] at ha ⊢
  have hadd : ∀ M N : Matrix (Fin S.rank) (Fin S.rank) (AE D), (M + N).map (Ideal.Quotient.mk (idAt D P)) =
      M.map (Ideal.Quotient.mk (idAt D P)) + N.map (Ideal.Quotient.mk (idAt D P)) :=
    fun M N => Matrix.map_add _ (Ideal.Quotient.mk (idAt D P)).map_add M N
  have key : (mt S (o.emb (a, 1))).map (Ideal.Quotient.mk (idAt D P)) =
      (o.jA ⬝ o.pA + o.jB ⬝ o.pB).map (Ideal.Quotient.mk (idAt D P)) := by
    rw [o.mt_emb, mt_one]; simp only [hadd, Matrix.map_mul, ha, Matrix.mul_one]
  rw [key, o.sum_eq_one]
  exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem inK_mul' {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a b : GA D S} (ha : InK S L P a) (hb : InK S L P b) :
    InK S L P (a * b) := by
  refine ⟨mul_mem ha.1 hb.1, fun y hy => ?_⟩
  have hy' : ∀ i, (mt S b *ᵥ y) i ∈ idAt D P := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  rw [mt_mul, ← Matrix.mulVec_mulVec, ← ha.2 _ hy', hb.2 y hy]

end GlobalTheory.FinPl.OrbitCoset

namespace GlobalTheory.FinPl.OrbitCoset

theorem orbit_coset : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ) (L : Lat B.V) (L₀ : Lat B.V₀) (v : Pl D), MonoAt B.d L L₀ v →
    ∀ n ∈ flagN B.d, n ∈ grpAt B.V (· = v) → ∀ a ∈ grpAt B.A (· = v), ∀ κ₀, InK B.V₀ L₀ (· = v) κ₀ → ∀ κ,
    InK B.V L (· = v) κ → ∃ r ∈ besGrp B.d B.o, r ∈ grpAt B.V (· = v) ∧ ∃ κ', InK B.V L (· = v) κ' ∧
      n * B.d.emb0 (B.o.emb (a, 1) * κ₀) * κ = r * κ' := by
  intro D σ B L L₀ v hM n hn hnv a ha κ₀ hκ₀ κ hκ
  refine ⟨n * embA B.d B.o a, mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨a, rfl⟩),
    mul_mem hnv (wittCoreEmbedding_mem_supportedSubgroup B.d _ (emb_mem_grpAt' B.o ha)), B.d.emb0 κ₀ * κ,
    inK_mul' ⟨wittCoreEmbedding_mem_supportedSubgroup B.d _ hκ₀.1, (carriesLattice_wittEmbedding_iff_core D B.V B.V₀ σ B.d L L₀ v κ₀ hM).2 hκ₀.2⟩ hκ, ?_⟩
  rw [map_mul, embA_apply]
  group

end GlobalTheory.FinPl.OrbitCoset

end
