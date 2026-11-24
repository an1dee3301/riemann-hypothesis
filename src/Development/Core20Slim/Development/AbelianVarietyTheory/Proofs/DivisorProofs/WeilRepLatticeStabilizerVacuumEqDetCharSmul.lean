module

public import Mathlib
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalVCutIdemOfNotMem
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryAdelicCharOfHeckeChar
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.Core20Slim.Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSelfDualAtScaled
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
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
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

noncomputable section

namespace GlobalTheory.VacStab

section General

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

theorem idem_mul_eq {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (ε : AF F)
    (e0 : ∀ w, evInf F w ε = 0) (e2 : ∀ u, u ≠ v → evFin F u ε = 0) {g h : GAd σ J}
    (e : proj σ J v g = proj σ J v h) (i j : Fin n) :
    algebraMap (AF F) (AF F ⊗[F] E) ε * (matHom _ σ J g).1 i j =
      algebraMap (AF F) (AF F ⊗[F] E) ε * (matHom _ σ J h).1 i j := by
  have c0 : ∀ w, compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) ε) = 0 := fun w => by
    change evInf F w ε ⊗ₜ[F] (1 : E) = 0
    rw [e0, TensorProduct.zero_tmul]
  have c2 : ∀ u, u ≠ v → compFin F E u (algebraMap (AF F) (AF F ⊗[F] E) ε) = 0 := fun u hu => by
    change evFin F u ε ⊗ₜ[F] (1 : E) = 0
    rw [e2 u hu, TensorProduct.zero_tmul]
  have e' : compFin F E v ((matHom _ σ J g).1 i j) = compFin F E v ((matHom _ σ J h).1 i j) :=
    congrArg (fun x => (matHom _ σ J x).1 i j) e
  rw [← sub_eq_zero, ← add_eq_right (b := 1)]
  refine Model.adTens_eq_one (fun w => ?_) fun u => ?_
  · rw [map_add (f := _), map_sub, map_mul, map_mul, c0, map_one]; simp
  · rw [map_add (f := _), map_sub, map_mul, map_mul, map_one]
    by_cases hu : u = v
    · subst hu; rw [e']; simp
    · rw [c2 u hu]; simp

end General

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory   
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def locPart (W : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : GA D W →* GA D W :=
  (GlobalTheory.AdelicU.emb D.sp.cm.sig W.gram v).comp (GlobalTheory.AdelicU.proj D.sp.cm.sig W.gram v)

theorem suppPl_locPart (W : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (k : GA D W) : GlobalTheory.WeilParts.SuppPl ε W (locPart W v k) :=
  (GlobalTheory.AdelicU.Model.suppF_iff W hε _).2 ⟨_, rfl⟩

theorem mt_locPart (W : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (k : GA D W) : Formalism.L2.Theta.mt W (locPart W v k) =
      algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt W k + (1 - algebraMap (AF D.host.F) (AE D) ε • 1) := by
  have h1 := suppPl_locPart W hε k
  obtain ⟨α, rfl, -, h2⟩ := hε
  ext i j
  have h3 : _ * Formalism.L2.Theta.mt W (locPart W v k) i j = _ * Formalism.L2.Theta.mt W k i j :=
    idem_mul_eq D.sp.cm.sig W.gram v (pairA D.host.F 0 α) (fun _ => rfl) h2
      (GlobalTheory.AdelicU.proj_emb_self D.sp.cm.sig W.gram v _) i j
  have h4 := h1 i j
  rw [Matrix.sub_apply] at h4
  rw [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  linear_combination h3 - h4






end GlobalTheory.VacStab

end
