module

public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Development.Core20Slim.Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import Development.Core20Slim.GroundTheory.AutomorphicForms.GL2.GodementSection
public import Development.Core20Slim.GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.GlobalZeta
public import Development.Core20Slim.GroundTheory.GlobalFields.TateThesis.HeckeChar
public import Init.Core
public import Init.Data.Cast
public import Init.Data.Nat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
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
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SProd
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Notation
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing

namespace PositivityTheory.RgEis.MG

open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

def avg {K : Subgroup G} [MeasurableSpace K] (μ : Measure K) (ρ : K →* (W →L[ℂ] W)) (φ : K → ℂ) : W →L[ℂ] W :=
  ∫ κ, φ κ • ρ κ ∂μ

def Law (K P : Subgroup G) (c : G → ℂ) (φ : K → ℂ) : Prop := ∀ r κ : K, (r : G) ∈ P → φ (r * κ) = c r * φ κ

def Near (K P : Subgroup G) (V : Set K) (φ : K → ℂ) : Prop :=
  ∀ κ, φ κ ≠ 0 → ∃ r v : K, (r : G) ∈ P ∧ v ∈ V ∧ κ = r * v ∧ ‖φ v - (‖φ v‖ : ℂ)‖ ≤ ‖φ v‖ / 4

def PolyEnt (a : ℂ → ℂ) : Prop :=
  Differentiable ℂ a ∧ ∀ b c : ℝ, ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ c → ‖a z‖ ≤ M * (1 + ‖z‖) ^ 2

structure PolyFam (Φ : ℂ → G → ℂ) : Prop where
  ent : ∀ g, Differentiable ℂ (Φ · g)
  cont : Continuous fun y : ℂ × G => Φ y.1 y.2
  strip : ∀ (a b : ℝ) (C : Set G), IsCompact C → ∃ M : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ∀ g ∈ C, ‖Φ z g‖ ≤ M * (1 + ‖z‖) ^ 2

structure LeftFam {T : Type} [TopologicalSpace T] (ζ : ℂ → T → ℂ) : Prop where
  hol : ∀ t, DifferentiableOn ℂ (ζ · t) {z | z.re < 1 / 2}
  cont : ContinuousOn (fun y : ℂ × T => ζ y.1 y.2) ({z | z.re < 1 / 2} ×ˢ Set.univ)
  strip : ∀ b c : ℝ, c < 1 / 2 → ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ c → ∀ t, ‖ζ z t‖ ≤ M * (1 + ‖z‖) ^ 2

end Abstract

def AvgMem : Prop := ForRep fun {G} _ _ {W} _ _ K ρ => ∀ [MeasurableSpace K] [BorelSpace K] (μ : Measure K), μ.IsHaarMeasure → IsProbabilityMeasure μ →
  ∀ (Γ P : Subgroup G) (c : G → ℂ), IsPar Γ K P c → ∀ φ : K → ℂ, Continuous φ → Law K P c φ → ∀ w : W,
    avg μ ρ φ w ∈ secSp K P c ρ

def AvgInv : Prop := ForRep fun {G} _ _ {W} _ _ K ρ => ∀ [MeasurableSpace K] [BorelSpace K] (μ : Measure K), μ.IsHaarMeasure → IsProbabilityMeasure μ →
  ∀ (Γ P : Subgroup G) (c : G → ℂ), IsPar Γ K P c → ∃ V ∈ 𝓝 (1 : K), ∀ φ : K → ℂ, Continuous φ → φ 1 = 1 → Law K P c φ →
    Near K P V φ → ∃ J : secSp K P c ρ →L[ℂ] W, ∀ w, avg μ ρ φ (J w) = w

def Unfold : Prop := ForRep fun {G} _ _ {W} _ _ K ρ => ∀ [MeasurableSpace K] [BorelSpace K] (μ : Measure K), μ.IsHaarMeasure → IsProbabilityMeasure μ →
  ∀ (Γ P : Subgroup G) (c : G → ℂ), IsPar Γ K P c → ∀ (φ : K → ℂ) (Λ T : G → ℂ), Continuous φ → Law K P c φ →
    (∀ g, ∀ κ ∈ K, Λ (g * κ) = Λ g) → (∀ p ∈ P, ∀ κ : K, T (p * κ) = c p * Complex.exp (Λ p) * φ κ) →
    ∀ (g : G) (u : Cos P Γ → ℝ), Summable u → (∀ q (κ : K), ‖T (rep q * (g * κ))‖ ≤ u q) → ∀ w : W,
      avg μ ρ (fun κ => ∑' q : Cos P Γ, T (rep q * (g * κ))) w = eis Γ K P c ρ Λ g (avg μ ρ φ w)

def DGood : Prop := ∀ (a : ℂ → ℂ) (N : ℂ), PolyEnt a →
  StripEntire (fun z => Complex.exp (z ^ 2) * a z) ∧ StripEntire fun z => (z - N) * (Complex.exp (z ^ 2) * a z)

def HGood : Prop := ForRep fun {G} _ _ {_W} _ _ K ρ => ∀ [MeasurableSpace K] [BorelSpace K] (μ : Measure K), μ.IsHaarMeasure → IsProbabilityMeasure μ →
  ∀ Φ : ℂ → G → ℂ, PolyFam Φ →
    (∀ g, Differentiable ℂ fun z => (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ fun κ => Φ z (g * κ)) ∧
    (Continuous fun y : ℂ × G => (Complex.exp (y.1 ^ 2) * (y.1 - 1)) • avg μ ρ fun κ => Φ y.1 (y.2 * κ)) ∧
    ∀ (b a : ℝ) (g : G), ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ a → ∀ g' ∈ U,
      ‖(Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ fun κ => Φ z (g' * κ)‖ ≤ M

def BGood : Prop := ForRep fun {_G} _ _ {_W} _ _ K ρ => ∀ [MeasurableSpace K] [BorelSpace K] (μ : Measure K), μ.IsHaarMeasure → IsProbabilityMeasure μ →
  ∀ ζ : ℂ → K → ℂ, LeftFam ζ →
    LeftGood (fun z => (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z)) (1 / 2) ∧
    LeftGood (fun z => z • (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z)) (1 / 2)

def Master : Prop := ForRep fun {G} _ _ {W} _ _ K ρ => ∀ [MeasurableSpace K] [BorelSpace K] (μ : Measure K), μ.IsHaarMeasure → IsProbabilityMeasure μ →
  ∀ (Γ P P' : Subgroup G) (c : G → ℂ) (η η' β : G → ℝ) (L : Submodule ℂ W) (J : L →L[ℂ] W) (R : ℝ) (N : ℂ)
    (Φ : ℂ → G → ℂ) (a : ℂ → ℂ) (ζ : ℂ → K → ℂ), IsPar Γ K P' c → L ≤ secSp K P c ρ → 0 ≤ R →
    (∀ x : ℝ, R < x → Conv Γ P fun g => x * η g) → (∀ x : ℝ, x < -R → Conv Γ P' fun g => β g - x * η' g) →
    PolyFam Φ → PolyEnt a → (∃ z, z ≠ N ∧ a z ≠ 0) → LeftFam ζ → (∀ z, Law K P' c (ζ z)) →
    (∀ z : ℂ, R < z.re → ∀ g (w : L), (z - 1) • avg μ ρ (fun κ => Φ z (g * κ)) (J w) =
      ((z - N) * a z) • eis Γ K P c ρ (fun x => z * η x) g w) →
    (∀ z : ℂ, z.re < -R → ∀ g (w : W), avg μ ρ (fun κ => Φ z (g * κ)) w =
      z • eis Γ K P' c ρ (fun x => β x - z * η' x) g (avg μ ρ (ζ z) w)) →
    ∃ Op H, Wall Γ K P P' c η η' β ρ L R (fun z => (z - N) * (Complex.exp (z ^ 2) * a z)) Op H ∧
      (∀ z g w, H z g w = (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (fun κ => Φ z (g * κ)) (J w)) ∧
      ∃ O : ℂ → (L →L[ℂ] secSp K P' c ρ), LeftGood O (1 / 2) ∧ ∀ z : ℂ, z.re < -R → Op z = z • O z

section Concrete

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

def dgl (d : ι → IdeleGroup k) : GL ι 𝔸[k] :=
  ⟨Matrix.diagonal fun i => (d i : 𝔸[k]), Matrix.diagonal fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k]),
    by rw [Matrix.diagonal_mul_diagonal]; simp, by rw [Matrix.diagonal_mul_diagonal]; simp⟩

variable {G : Type} [Group G]

def kap (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (g : G) : GL ι 𝔸[k] := (dgl d)⁻¹ * π g * dgl d

def vec (m : GL ι 𝔸[k]) (i : ι) : ι → 𝔸[k] := ((m⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i 1

def zt (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (g : G) : ℂ :=
  lineZeta Ψ ω s (vec (kap π d g) i)

def tate (Ψ₁ : (Unit → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) : ℂ := globalZeta (fun t => Ψ₁ fun _ => t) ω s

structure Side [TopologicalSpace G] (π : G →* GL ι 𝔸[k]) (Γ K P : Subgroup G) (i : ι) (ω : HeckeCharacter k)
    (d : ι → IdeleGroup k) (c : G → ℂ) (η : G → ℝ) : Prop where
  two : 2 ≤ Fintype.card ι
  sq : ω * ω = 1
  cont : Continuous π
  piK : ∀ κ ∈ K, kap π d κ ∈ (adStd k).kGL ι
  piΓ : ∀ γ ∈ Γ, π γ ∈ (adStd k).ratGL ι
  trans : ∀ g ∈ (adStd k).ratGL ι, ∃ γ ∈ Γ, g * (π γ)⁻¹ ∈ stab 𝔸[k] {i}
  mem : ∀ g, g ∈ P ↔ π g ∈ stab 𝔸[k] {i}
  par : IsPar Γ K P c
  ht : IsHt Γ K P η
  val : ∀ p ∈ P, c p = ω.toIdele (bdet {i} (π p)) ∧ η p = (adStd k).lg (bdet {i} (π p))

end Concrete

def SideOf : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (K : Subgroup G), IsCompact (K : Set G) →
  ∀ (k : Type) [Field k] [NumberField k] (ι : Type) [Fintype ι] [DecidableEq ι] (π : G →* GL ι 𝔸[k]) (Γ : Subgroup G)
  (i₀ i₁ : ι) (ω : HeckeCharacter k) (d : ι → IdeleGroup k) (c : G → ℂ) (η η' l : G → ℝ), MirData π Γ K i₀ i₁ ω d c η η' l →
    Side π Γ K ((stab 𝔸[k] {i₀}).comap π) i₀ ω d c η ∧
    Side (tInv.comp π) Γ K ((stab 𝔸[k] {i₁}ᶜ).comap π) i₁ ω (fun i => (d i)⁻¹) c η' ∧
    (∀ g, tInv (π g * dgl d) = (tInv.comp π) g * dgl fun i => (d i)⁻¹) ∧
    ∀ g, modPow (Matrix.GeneralLinearGroup.det (π g * dgl d)) 1 =
      Complex.exp (l g) * modPow (Matrix.GeneralLinearGroup.det (dgl d)) 1

def Lines : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (K : Subgroup G), IsCompact (K : Set G) →
  ∀ (k : Type) [Field k] [NumberField k] (ι : Type) [Fintype ι] [DecidableEq ι] (π : G →* GL ι 𝔸[k]) (Γ P : Subgroup G)
  (i : ι) (ω : HeckeCharacter k) (d : ι → IdeleGroup k) (c : G → ℂ) (η : G → ℝ), Side π Γ K P i ω d c η →
    ∃ e : Cos P Γ ≃ Projectivization k (ι → k), ∀ q, ∃ x : kˣ,
      ratV (e q).rep = algebraMap k 𝔸[k] x • vec (π (rep q)) i

def Term : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (K : Subgroup G), IsCompact (K : Set G) →
  ∀ (k : Type) [Field k] [NumberField k] (ι : Type) [Fintype ι] [DecidableEq ι] (π : G →* GL ι 𝔸[k]) (Γ P : Subgroup G)
  (i : ι) (ω : HeckeCharacter k) (d : ι → IdeleGroup k) (c : G → ℂ) (η : G → ℝ), Side π Γ K P i ω d c η →
    (∀ p ∈ P, ∀ κ ∈ K, vec (π (p * κ) * dgl d) i =
      (((bdet {i} (π p) * d i)⁻¹ : IdeleGroup k) : 𝔸[k]) • vec (kap π d κ) i) ∧
    ∀ (Ψ : (ι → 𝔸[k]) → ℂ) (s : ℂ),
      (∀ p ∈ P, ∀ κ ∈ K, lineZeta Ψ ω s (vec (π (p * κ) * dgl d) i) =
        c p * Complex.exp (s * η p) * ((ω.toIdele (d i) : ℂ) * modPow (d i) s * zt π d i Ψ ω s κ)) ∧
      (Law K P c fun κ => zt π d i Ψ ω s κ) ∧
      ∀ (x : kˣ) (v : ι → 𝔸[k]), lineZeta Ψ ω s (algebraMap k 𝔸[k] x • v) = lineZeta Ψ ω s v

def ZetaK : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (K : Subgroup G), IsCompact (K : Set G) →
  ∀ (k : Type) [Field k] [NumberField k] (ι : Type) [Fintype ι] [DecidableEq ι] (π : G →* GL ι 𝔸[k]) (Γ P : Subgroup G)
  (i : ι) (ω : HeckeCharacter k) (d : ι → IdeleGroup k) (c : G → ℂ) (η : G → ℝ), Side π Γ K P i ω d c η →
    ∀ Ψ ∈ GJMatrix.schwartzBruhatPi (K := k) (ι := ι),
      (∀ κ : K, DifferentiableOn ℂ (fun s => zt π d i Ψ ω s κ) {s | 1 < s.re}) ∧
      ContinuousOn (fun y : ℂ × K => zt π d i Ψ ω y.1 y.2) ({s | 1 < s.re} ×ˢ Set.univ) ∧
      ∀ a b : ℝ, 1 < a → ∃ M : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ∀ κ : K, ‖zt π d i Ψ ω s κ‖ ≤ M

def SideUnfold : Prop := ForRep fun {G} _ _ {W} _ _ K ρ => ∀ [MeasurableSpace K] [BorelSpace K] (μ : Measure K), μ.IsHaarMeasure → IsProbabilityMeasure μ →
  ∀ (k : Type) [Field k] [NumberField k] (ι : Type) [Fintype ι] [DecidableEq ι] (π : G →* GL ι 𝔸[k]) (Γ P : Subgroup G)
  (i : ι) (ω : HeckeCharacter k) (d : ι → IdeleGroup k) (c : G → ℂ) (η : G → ℝ), Side π Γ K P i ω d c η →
    ∀ Ψ ∈ GJMatrix.schwartzBruhatPi (K := k) (ι := ι), ∀ s : ℂ, (Fintype.card ι : ℝ) < s.re → ∀ (g : G) (w : W),
      avg μ ρ (fun κ => epstein Ψ ω s (π (g * κ) * dgl d)) w =
        ((ω.toIdele (d i) : ℂ) * modPow (d i) s) •
          eis Γ K P c ρ (fun x => s * η x) g (avg μ ρ (fun κ => zt π d i Ψ ω s κ) w)

def SideConv : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (K : Subgroup G), IsCompact (K : Set G) →
  ∀ (k : Type) [Field k] [NumberField k] (ι : Type) [Fintype ι] [DecidableEq ι] (π : G →* GL ι 𝔸[k]) (Γ P : Subgroup G)
  (i : ι) (ω : HeckeCharacter k) (d : ι → IdeleGroup k) (c : G → ℂ) (η : G → ℝ), Side π Γ K P i ω d c η →
    ∀ x : ℝ, (Fintype.card ι : ℝ) < x → Conv Γ P fun g => x * η g

def TestK : Prop := ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (K : Subgroup G), IsCompact (K : Set G) →
  ∀ (k : Type) [Field k] [NumberField k] (ι : Type) [Fintype ι] [DecidableEq ι] (π : G →* GL ι 𝔸[k]) (Γ P : Subgroup G)
  (i : ι) (ω : HeckeCharacter k) (d : ι → IdeleGroup k) (c : G → ℂ) (η : G → ℝ), Side π Γ K P i ω d c η →
    ∀ V ∈ 𝓝 (1 : K), ∃ (Ψ : (ι → 𝔸[k]) → ℂ) (Ψ₁ : (Unit → 𝔸[k]) → ℂ) (φ : K → ℂ),
      Ψ ∈ GJMatrix.schwartzBruhatPi (K := k) (ι := ι) ∧ Ψ₁ ∈ GJMatrix.schwartzBruhatPi (K := k) (ι := Unit) ∧ Continuous φ ∧ φ 1 = 1 ∧ Law K P c φ ∧
      Near K P V φ ∧ (∀ s (κ : K), zt π d i Ψ ω s κ = tate Ψ₁ ω s * φ κ) ∧
      (∃ z : ℂ, (Fintype.card ι : ℝ) < z.re ∧ tate Ψ₁ ω z ≠ 0) ∧ (ω = 1 → ∀ x : ℝ, 1 < x → tate Ψ₁ ω x ≠ 0)

def ZetaOne : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (Ψ₁ : (Unit → 𝔸[k]) → ℂ) (ω : HeckeCharacter k),
    Ψ₁ ∈ GJMatrix.schwartzBruhatPi (K := k) (ι := Unit) → ω * ω = 1 →
    ∃ a : ℂ → ℂ, PolyEnt a ∧ ∀ z : ℂ, 1 < z.re → a z = z * (z - 1) * tate Ψ₁ ω z

def Core : Prop := ForRep fun {G} _ _ {W} _ _ K ρ => ∀ [MeasurableSpace K] [BorelSpace K] (μ : Measure K), μ.IsHaarMeasure → IsProbabilityMeasure μ →
  ∀ (k : Type) [Field k] [NumberField k] (ι : Type) [Fintype ι] [DecidableEq ι] (π : G →* GL ι 𝔸[k]) (Γ : Subgroup G)
  (i₀ i₁ : ι) (ω : HeckeCharacter k) (d : ι → IdeleGroup k) (c : G → ℂ) (η η' l : G → ℝ), MirData π Γ K i₀ i₁ ω d c η η' l →
    ∀ (Ψ : (ι → 𝔸[k]) → ℂ) (Ψ₁ : (Unit → 𝔸[k]) → ℂ) (φ : K → ℂ) (L : Submodule ℂ W) (J : L →L[ℂ] W),
    Ψ ∈ GJMatrix.schwartzBruhatPi (K := k) (ι := ι) → Ψ₁ ∈ GJMatrix.schwartzBruhatPi (K := k) (ι := Unit) →
    (∀ s (κ : K), zt π d i₀ Ψ ω s κ = tate Ψ₁ ω s * φ κ) → (∃ z : ℂ, (Fintype.card ι : ℝ) < z.re ∧ tate Ψ₁ ω z ≠ 0) →
    L ≤ secSp K ((stab 𝔸[k] {i₀}).comap π) c ρ → (∀ w, avg μ ρ φ (J w) = w) →
    ∃ R D Op H, Wall Γ K ((stab 𝔸[k] {i₀}).comap π) ((stab 𝔸[k] {i₁}ᶜ).comap π) c η η'
        (fun g => l g + (Fintype.card ι : ℝ) * η' g) ρ L R D Op H ∧
      (∃ dd : ℂ → ℂ, StripEntire dd ∧ (∀ z, D z = (z - (Fintype.card ι : ℝ)) * dd z) ∧
        (tate Ψ₁ ω (Fintype.card ι : ℝ) ≠ 0 → dd (Fintype.card ι : ℝ) ≠ 0)) ∧
      (∃ O : ℂ → (L →L[ℂ] secSp K ((stab 𝔸[k] {i₁}ᶜ).comap π) c ρ), LeftGood O (1 / 2) ∧
        ∀ z : ℂ, z.re < -R → Op z = z • O z) ∧
      (ω = 1 → (∃ a : ℂ, a ≠ 0 ∧ ∀ g w, H 0 g w = (a * Ψ 0) • avg μ ρ (fun _ => 1) (J w)) ∧
        ∃ b : ℂ, ∀ g w, H (Fintype.card ι : ℝ) g w = (Complex.exp (l g) * b) • avg μ ρ (fun _ => 1) (J w))

end PositivityTheory.RgEis.MG
