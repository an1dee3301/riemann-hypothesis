module

public import Mathlib
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements
public import Development.Core20Slim.GroundTheory.AutomorphicForms.HermitianSpaces
public import Development.Core20Slim.GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Fin.Basic
public import Init.Data.Int.Basic
public import Init.Data.Nat.Basic
public import Init.Data.NeZero
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.Orientation
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Init
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

section MatrixLevel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def IsMajorantOf (H P : Matrix ι ι ℂ) : Prop :=
  P.PosDef ∧ H.IsHermitian ∧ IsUnit H.det ∧ P * H⁻¹ * P = H

def majInvolution (H P : Matrix ι ι ℂ) : Matrix ι ι ℂ := H⁻¹ * P

def plusPart (H P : Matrix ι ι ℂ) (z : ι → ℂ) : ι → ℂ :=
  (1 / 2 : ℂ) • (z + majInvolution H P *ᵥ z)

def minusPart (H P : Matrix ι ι ℂ) (z : ι → ℂ) : ι → ℂ :=
  (1 / 2 : ℂ) • (z - majInvolution H P *ᵥ z)

def pReflection (P : Matrix ι ι ℂ) (v : ι → ℂ) : Matrix ι ι ℂ :=
  1 - (2 / (star v ⬝ᵥ (P *ᵥ v))) • (vecMulVec v (star v) * P)

def phaseOnMinus (H P : Matrix ι ι ℂ) (c : ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • (1 + majInvolution H P) + (c / 2) • (1 - majInvolution H P)

variable (ι)

def MajorantBound.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ z : ι → ℂ,
    ‖star z ⬝ᵥ (H *ᵥ z)‖ ≤ (star z ⬝ᵥ (P *ᵥ z)).re

def EigenspacesOrthogonal.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ a b : ι → ℂ,
    majInvolution H P *ᵥ a = a → majInvolution H P *ᵥ b = -b → star a ⬝ᵥ (P *ᵥ b) = 0

def IsotropicSplit.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ z : ι → ℂ, star z ⬝ᵥ (H *ᵥ z) = 0 →
    majInvolution H P *ᵥ plusPart H P z = plusPart H P z ∧
    majInvolution H P *ᵥ minusPart H P z = -minusPart H P z ∧
    star (plusPart H P z) ⬝ᵥ (P *ᵥ plusPart H P z) =
      star (minusPart H P z) ⬝ᵥ (P *ᵥ minusPart H P z)

def EigenReflection.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ ε : ℂ, (ε = 1 ∨ ε = -1) → ∀ v : ι → ℂ, v ≠ 0 →
    majInvolution H P *ᵥ v = ε • v →
    (pReflection P v)ᴴ * P * pReflection P v = P ∧ (pReflection P v)ᴴ * H * pReflection P v = H ∧
      pReflection P v *ᵥ v = -v ∧ ∀ u : ι → ℂ, star v ⬝ᵥ (P *ᵥ u) = 0 → pReflection P v *ᵥ u = u

def EigenReflectionMaps.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ ε : ℂ, (ε = 1 ∨ ε = -1) → ∀ a a' : ι → ℂ,
    majInvolution H P *ᵥ a = ε • a → majInvolution H P *ᵥ a' = ε • a' →
    star a ⬝ᵥ (P *ᵥ a) = star a' ⬝ᵥ (P *ᵥ a') →
    ∃ α : ℂ, ‖α‖ = 1 ∧ ∃ R : Matrix ι ι ℂ, Rᴴ * P * R = P ∧ Rᴴ * H * R = H ∧ R *ᵥ a' = α • a ∧
      ∀ u : ι → ℂ, majInvolution H P *ᵥ u = (-ε) • u → R *ᵥ u = u

def PhaseOnMinus.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ c : ℂ, ‖c‖ = 1 →
    (phaseOnMinus H P c)ᴴ * P * phaseOnMinus H P c = P ∧
      (phaseOnMinus H P c)ᴴ * H * phaseOnMinus H P c = H ∧
      (∀ u : ι → ℂ, majInvolution H P *ᵥ u = u → phaseOnMinus H P c *ᵥ u = u) ∧
      (∀ u : ι → ℂ, majInvolution H P *ᵥ u = -u → phaseOnMinus H P c *ᵥ u = c • u)

def KTransitive.Statement : Prop :=
  ∀ H P : Matrix ι ι ℂ, IsMajorantOf H P → ∀ z z' : ι → ℂ, z ≠ 0 → z' ≠ 0 →
    star z ⬝ᵥ (H *ᵥ z) = 0 → star z' ⬝ᵥ (H *ᵥ z') = 0 →
    ∃ k : GL ι ℂ, k ∈ unitaryGroupMatrix (starRingEnd ℂ) H ∧
      k ∈ unitaryGroupMatrix (starRingEnd ℂ) P ∧ ∃ c : ℂ, (k : Matrix ι ι ℂ) *ᵥ z' = c • z

end MatrixLevel

section Places

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def HermAtPlace.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (w : InfinitePlace E) (x y : W),
    w.embedding (h.toSesq x y) = star (vecAt v x w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v y w)

def GramAtData.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ w : InfinitePlace E, (gramAt h v w).IsHermitian ∧ IsUnit (gramAt h v w).det

def ArchInvariant.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (g : archUnitary h v) (y z : InfinitePlace E → ι → ℂ) (w : InfinitePlace E),
    star (invApply g y w) ⬝ᵥ (gramAt h v w *ᵥ invApply g z w) =
      star (y w) ⬝ᵥ (gramAt h v w *ᵥ z w)

def LenSq.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (y : InfinitePlace E → ι → ℂ),
    (∀ w, 0 ≤ (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re) ∧
      M.len y ^ 2 = ∑ w, (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re

def VecAtNeZero.Statement (v : Basis ι E W) : Prop :=
  ∀ x : W, x ≠ 0 → ∀ w : InfinitePlace E, vecAt v x w ≠ 0


variable (E) in
def IntegerSmallAtPlaces.Statement : Prop :=
  ∀ a ∈ integralClosure ℤ E, (∀ w : InfinitePlace E, w a < 1) → a = 0

end Places

section Line

variable {E : Type*} [Field E] [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W]


variable (E) in
def intSubgroup : AddSubgroup E := (algebraMap (𝓞 E) E).toAddMonoidHom.range

def lineCoeffs (La : AddSubgroup W) (x : W) : AddSubgroup E :=
  La.comap ((smulAddHom E W).flip x)

def weightedEmbed (c : InfinitePlace E → ℝ) : E →+ EuclideanSpace ℝ (InfinitePlace E × Fin 2) where
  toFun a := WithLp.toLp 2 fun p =>
    Real.sqrt (c p.1) * (if p.2 = 0 then (p.1.embedding a).re else (p.1.embedding a).im)
  map_zero' := by
    ext p
    simp
  map_add' a b := by
    ext p
    simp only [map_add (f := _), Complex.add_re, Complex.add_im, PiLp.add_apply]
    split_ifs <;> ring


variable (W) in
def LineIndexCoeffs.Statement : Prop :=
  ∀ (La : AddSubgroup W) (x : W), x ≠ 0 →
    lineIndex E La x = (intSubgroup E).relIndex (lineCoeffs La x)


variable (W) in
def LineCoeffsFG.Statement : Prop :=
  ∀ (La : AddSubgroup W) (x : W), La.FG → x ≠ 0 → (lineCoeffs (E := E) La x).FG

variable (E)

def CoeffLatticeBasis.Statement : Prop :=
  ∀ A : AddSubgroup E, intSubgroup E ≤ A → A.FG → Nonempty (Basis (Fin (finrank ℚ E)) ℤ A)

def IndexLeDet.Statement : Prop :=
  ∀ A : AddSubgroup E, intSubgroup E ≤ A → ∀ (e : Basis (Fin (finrank ℚ E)) ℤ A)
    (a : Fin (finrank ℚ E) → 𝓞 E) (T : Matrix (Fin (finrank ℚ E)) (Fin (finrank ℚ E)) ℤ),
    LinearIndependent ℚ (fun i => (a i : E)) → (∀ i, (a i : E) = ∑ j, T i j • (e j : E)) →
    ((intSubgroup E).relIndex A : ℝ) ≤ |(T.det : ℝ)|

def WeightedNormSq.Statement : Prop :=
  ∀ c : InfinitePlace E → ℝ, (∀ w, 0 ≤ c w) → ∀ a : E,
    ‖weightedEmbed c a‖ ^ 2 = ∑ w, c w * ‖w.embedding a‖ ^ 2

def WeightedSpaceDim.Statement [_root_.NumberField.IsTotallyComplex E] : Prop :=
  finrank ℝ (EuclideanSpace ℝ (InfinitePlace E × Fin 2)) = finrank ℚ E

def WeightedIndexBound.Statement [_root_.NumberField.IsTotallyComplex E] : Prop :=
  ∀ c : InfinitePlace E → ℝ, (∀ w, 0 < c w) → ∀ A : AddSubgroup E, intSubgroup E ≤ A → A.FG →
    (∀ a ∈ A, a ≠ 0 → ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2) →
    ∀ r : ℝ, (∃ a : Fin (finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (a i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (a i)‖ ≤ r) →
    ((intSubgroup E).relIndex A : ℝ) ≤ (r * Real.sqrt (finrank ℚ E)) ^ finrank ℚ E

end Line

section Minkowski

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (d : ℕ) [Fact (finrank ℝ V = d)]

def MinkowskiVolumeForm.Statement : Prop :=
  ∀ (o : Orientation ℝ V (Fin d)) (b : Fin d → V) (lam : ℝ), 0 < lam →
    (∀ z : Fin d → ℤ, z ≠ 0 → lam ≤ ‖∑ i, (z i : ℝ) • b i‖) →
    (lam / Real.sqrt d) ^ d ≤ |o.volumeForm b|

def VolumeFormIntComb.Statement : Prop :=
  ∀ (o : Orientation ℝ V (Fin d)) (b : Fin d → V) (T : Matrix (Fin d) (Fin d) ℤ),
    o.volumeForm (fun i => ∑ j, (T i j : ℝ) • b j) = (T.det : ℝ) * o.volumeForm b

end Minkowski

section Steps

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def WeightedLenSmul.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (g : archUnitary h v) (x : W) (a : E),
    M.len (invApply g (vecAt v (a • x))) ^ 2 =
      ∑ w, ‖w.embedding a‖ ^ 2 *
        (star (invApply g (vecAt v x) w) ⬝ᵥ (M.P w *ᵥ invApply g (vecAt v x) w)).re

def WeightPos.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (g : archUnitary h v) (x : W), x ≠ 0 → ∀ w : InfinitePlace E,
    0 < (star (invApply g (vecAt v x) w) ⬝ᵥ (M.P w *ᵥ invApply g (vecAt v x) w)).re

end Steps

section Inhabitants

open GaussianPlane



end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
