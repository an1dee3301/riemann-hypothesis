module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Core
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
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open MeasureTheory
open GlobalTheory.Mem.Isom
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri Rig)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriMove

variable {D : D7}

def rdx {K : Type} [Zero K] [One K] {m n : ℕ} (h : m = n) : Matrix (Fin m) (Fin n) K :=
  (1 : Matrix (Fin m) (Fin m) K).submatrix id (finCongr h).symm

def rdi {K : Type} [Zero K] [One K] {m n : ℕ} (h : m = n) : Matrix (Fin n) (Fin m) K :=
  (1 : Matrix (Fin m) (Fin m) K).submatrix (finCongr h).symm id

theorem rdx_rdi {K : Type} [CommRing K] {m n : ℕ} (h : m = n) : rdx (K := K) h * rdi (K := K) h = 1 := by
  subst h
  ext i j
  simp [rdx, rdi, Matrix.one_apply]

theorem rdi_rdx {K : Type} [CommRing K] {m n : ℕ} (h : m = n) : rdi (K := K) h * rdx (K := K) h = 1 := by
  subst h
  ext i j
  simp [rdx, rdi, Matrix.one_apply]

def glMove {K : Type} [CommRing K] {m n : ℕ} (h : m = n) (P : Matrix (Fin n) (Fin m) K) (Q : Matrix (Fin m) (Fin n) K)
    (PQ : P * Q = 1) (QP : Q * P = 1) (x : GL (Fin m) K) : GL (Fin n) K where
  val := HMul.hMul (HMul.hMul P (x.1 : Matrix (Fin m) (Fin m) K)) (rdx (K := K) h)
  inv := HMul.hMul (HMul.hMul (rdi (K := K) h) (x.2 : Matrix (Fin m) (Fin m) K)) Q
  val_inv := by
    have e1 := rdx_rdi (K := K) h
    have e2 : (x.1 : Matrix (Fin m) (Fin m) K) * x.2 = 1 := x.val_inv
    calc HMul.hMul (HMul.hMul (HMul.hMul P (x.1 : Matrix (Fin m) (Fin m) K)) (rdx (K := K) h))
          (HMul.hMul (HMul.hMul (rdi (K := K) h) (x.2 : Matrix (Fin m) (Fin m) K)) Q)
        = HMul.hMul (HMul.hMul P (HMul.hMul (HMul.hMul (x.1 : Matrix (Fin m) (Fin m) K) (HMul.hMul (rdx (K := K) h) (rdi (K := K) h))) (x.2 : Matrix (Fin m) (Fin m) K))) Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e1, Matrix.mul_one, e2, Matrix.mul_one, PQ]
  inv_val := by
    have e1 := rdi_rdx (K := K) h
    have e2 : (x.2 : Matrix (Fin m) (Fin m) K) * x.1 = 1 := x.inv_val
    calc HMul.hMul (HMul.hMul (HMul.hMul (rdi (K := K) h) (x.2 : Matrix (Fin m) (Fin m) K)) Q)
          (HMul.hMul (HMul.hMul P (x.1 : Matrix (Fin m) (Fin m) K)) (rdx (K := K) h))
        = HMul.hMul (HMul.hMul (rdi (K := K) h) (HMul.hMul (HMul.hMul (x.2 : Matrix (Fin m) (Fin m) K) (HMul.hMul Q P)) (x.1 : Matrix (Fin m) (Fin m) K))) (rdx (K := K) h) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [QP, Matrix.mul_one, e2, Matrix.mul_one, e1]

variable {S S' T T' : HSp D}

def fP (I : IsoMat S S') : Matrix (Fin S'.rank) (Fin S.rank) (Lev.EAf D) := I.P.map (eToEAf D)

def fQ (I : IsoMat S S') : Matrix (Fin S.rank) (Fin S'.rank) (Lev.EAf D) := I.Q.map (eToEAf D)

theorem fP_fQ (I : IsoMat S S') : fP I * fQ I = 1 := by
  rw [fP, fQ, ← Matrix.map_mul, I.PQ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem fQ_fP (I : IsoMat S S') : fQ I * fP I = 1 := by
  rw [fP, fQ, ← Matrix.map_mul, I.QP, Matrix.map_one _ (map_zero _) (map_one _)]

def betaMove (I : IsoMat S S') (β : GL (Fin S.rank) (Lev.EAf D)) : GL (Fin S'.rank) (Lev.EAf D) :=
  glMove I.rank_eq (fP I) (fQ I) (fP_fQ I) (fQ_fP I) β

def latMove (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E) :=
  Λ.map ((Matrix.mulVecLin I.P).restrictScalars (𝓞 D.host.E))

def cartMove (I : IsoMat S S') (τ : D.what₂.Tau) (s : Matrix (Fin S.rank) (Fin S.rank) ℂ) :
    Matrix (Fin S'.rank) (Fin S'.rank) ℂ := I.pT τ * s * I.qT τ

def basMove (I : IsoMat S S') (τ : D.what₂.Tau) (B : Matrix (Fin S.rank) (Fin S.rank) ℂ) :
    Matrix (Fin S'.rank) (Fin S'.rank) ℂ := I.pT τ * B * rdx I.rank_eq

def rigMove (I : IsoMat S S') (r : Rig S) : Rig S' where
  Λ := latMove I r.Λ
  β := betaMove I r.β
  s τ := cartMove I τ (r.s τ)
  B τ := basMove I τ (r.B τ)

def homMap (IS : IsoMat S S') (IT : IsoMat T T') : WO S T ≃+ WO S' T' where
  toFun x := HMul.hMul (HMul.hMul IT.aP x) IS.aQ
  invFun y := HMul.hMul (HMul.hMul IT.aQ y) IS.aP
  left_inv x := by
    show HMul.hMul (HMul.hMul IT.aQ (HMul.hMul (HMul.hMul IT.aP x) IS.aQ)) IS.aP = x
    calc _ = HMul.hMul (HMul.hMul (HMul.hMul IT.aQ IT.aP) x) (HMul.hMul IS.aQ IS.aP) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [IT.aQ_aP, IS.aQ_aP, Matrix.one_mul, Matrix.mul_one]
  right_inv y := by
    show HMul.hMul (HMul.hMul IT.aP (HMul.hMul (HMul.hMul IT.aQ y) IS.aP)) IS.aQ = y
    calc _ = HMul.hMul (HMul.hMul (HMul.hMul IT.aP IT.aQ) y) (HMul.hMul IS.aP IS.aQ) := by simp only [Matrix.mul_assoc]
      _ = y := by rw [IT.aP_aQ, IS.aP_aQ, Matrix.one_mul, Matrix.mul_one]
  map_add' x y := by
    show HMul.hMul (HMul.hMul IT.aP (x + y)) IS.aQ = HMul.hMul (HMul.hMul IT.aP x) IS.aQ + HMul.hMul (HMul.hMul IT.aP y) IS.aQ
    rw [Matrix.mul_add, Matrix.add_mul]

theorem homMap_apply (IS : IsoMat S S') (IT : IsoMat T T') (x : WO S T) :
    homMap IS IT x = HMul.hMul (HMul.hMul IT.aP x) IS.aQ := rfl

def trH (IS : IsoMat S S') (IT : IsoMat T T') (f : WO S T → ℂ) : WO S' T' → ℂ := fun w => f ((homMap IS IT).symm w)

def trLE (IS : IsoMat S S') (IT : IsoMat T T') : (WO S T → ℂ) ≃ₗ[ℂ] (WO S' T' → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (homMap IS IT).symm.toEquiv

def omH (IS : IsoMat S S') (IT : IsoMat T T') (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) :
    GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ) :=
  (trLE IS IT).conjRingEquiv.toMulEquiv.toMonoidHom.comp (om.comp (IS.kap.symm.toMonoidHom.prodMap IT.kap.symm.toMonoidHom))

theorem omH_apply (IS : IsoMat S S') (IT : IsoMat T T') (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (g : GA D S') (h : GA D T') (f : WO S' T' → ℂ) :
    omH IS IT om (g, h) f = trH IS IT (om (IS.kap.symm g, IT.kap.symm h) (trH IS.symm IT.symm f)) := rfl

def polMove {m n m' n' : ℕ} (hm : m = m') (hn : n = n') :
    MvPolynomial (FVar D m n) ℂ →ₐ[ℂ] MvPolynomial (FVar D m' n') ℂ :=
  MvPolynomial.rename fun k => (k.1, finCongr hm k.2.1, finCongr hn k.2.2)

variable {T₀ : Type} {A A' WW B B' WW₁ : HSp D}

def triMove (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁) : Tri T₀ A A' WW where
  rA := rigMove IA Y.rA
  rA' := rigMove IA' Y.rA'
  rW := rigMove IW Y.rW
  ω t := omH IA IW (Y.ω t)
  ω' t := omH IA' IW (Y.ω' t)
  vac := trH IA IW Y.vac
  vac' := trH IA' IW Y.vac'
  e := Y.e
  c := Y.c
  f t := trH IA IW (Y.f t)
  f' t := trH IA' IW (Y.f' t)
  m := Y.m.map IA.kap
  fd := IA.kap.symm ⁻¹' Y.fd
  m' := Y.m'.map IA'.kap
  fd' := IA'.kap.symm ⁻¹' Y.fd'

end GlobalTheory.TriMove

end
