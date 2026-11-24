module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.Core20Slim.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSmulNeBot
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Init.Classical
public import Init.Core
public import Init.Data.Int.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Data.Zero
public import Init.Prelude
public import Init.SimpLemmas
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.StdSumFix

variable {D : D7}

theorem hatId_mul_left {𝔪 : Ideal (𝓞 D.host.E)} {t y : AE D} (ht : t ∈ OhE D) (hy : y ∈ hatId D 𝔪) :
    t * y ∈ hatId D 𝔪 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, t * s, mul_mem ht hs, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

abbrev mat {N : ℕ} (k : GA D N) : Matrix (Fin N) (Fin N) (AE D) := ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))

theorem mat_mul {N : ℕ} (x y : GA D N) : mat (x * y) = mat x * mat y := rfl

theorem mat_inv_mul {N : ℕ} (x : GA D N) : mat x⁻¹ * mat x = 1 := by
  simp [mat]

theorem mat_mul_inv {N : ℕ} (x : GA D N) : mat x * mat x⁻¹ = 1 := by
  simp [mat]

theorem ent_mul_left {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {A B : Matrix (Fin N) (Fin N) (AE D)}
    (hA : ∀ i j, A i j ∈ OhE D) (hB : ∀ i j, B i j ∈ hatId D 𝔪) (i j : Fin N) : (A * B) i j ∈ hatId D 𝔪 := by
  rw [Matrix.mul_apply]; exact sum_mem fun l _ => hatId_mul_left (hA i l) (hB l j)

theorem ent_mul_right {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {A B : Matrix (Fin N) (Fin N) (AE D)}
    (hB : ∀ i j, B i j ∈ hatId D 𝔪) (hA : ∀ i j, A i j ∈ OhE D) (i j : Fin N) : (B * A) i j ∈ hatId D 𝔪 := by
  rw [Matrix.mul_apply]; exact sum_mem fun l _ => by rw [mul_comm]; exact hatId_mul_left (hA l j) (hB i l)

theorem ent_of_mem {N : ℕ} {k : GA D N} (hk : k ∈ intG D N) (i j : Fin N) : mat k i j ∈ OhE D :=
  ((mem_intG k).1 hk i j).1

theorem ent_inv_of_mem {N : ℕ} {k : GA D N} (hk : k ∈ intG D N) (i j : Fin N) : mat k⁻¹ i j ∈ OhE D :=
  ((mem_intG k⁻¹).1 (inv_mem hk) i j).1

variable {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ}

theorem congOne_one : CongOne D 𝔪 (1 : GA D N) := fun i j => by
  simp only [OneMemClass.coe_one, Units.val_one, sub_self, Matrix.zero_apply]; exact zero_mem _

theorem congOne_mul {x y : GA D N} (hx : x ∈ intG D N) (cx : CongOne D 𝔪 x) (cy : CongOne D 𝔪 y) :
    CongOne D 𝔪 (x * y) := fun i j => by
  have e : mat (x * y) - 1 = mat x * (mat y - 1) + (mat x - 1) := by rw [mat_mul, mul_sub, mul_one]; abel
  change (mat (x * y) - 1) i j ∈ _
  rw [e, Matrix.add_apply]
  exact add_mem (ent_mul_left (ent_of_mem hx) cy i j) (cx i j)

theorem congOne_inv {x : GA D N} (hx : x ∈ intG D N) (cx : CongOne D 𝔪 x) : CongOne D 𝔪 x⁻¹ := fun i j => by
  have e : mat x⁻¹ - 1 = -(mat x⁻¹ * (mat x - 1)) := by rw [mul_sub, mat_inv_mul, mul_one]; abel
  change (mat x⁻¹ - 1) i j ∈ _
  rw [e, Matrix.neg_apply]
  exact neg_mem (ent_mul_left (ent_inv_of_mem hx) cx i j)

theorem congOne_conj {g x : GA D N} (hg : g ∈ intG D N) (cx : CongOne D 𝔪 x) : CongOne D 𝔪 (g * x * g⁻¹) :=
  fun i j => by
  have e : mat (g * x * g⁻¹) - 1 = mat g * (mat x - 1) * mat g⁻¹ := by
    rw [mat_mul, mat_mul, mul_sub, sub_mul, mul_one, mat_mul_inv]
  change (mat (g * x * g⁻¹) - 1) i j ∈ _
  rw [e]
  exact ent_mul_right (ent_mul_left (ent_of_mem hg) cx) (ent_inv_of_mem hg) i j

end GlobalTheory.StdSumFix

namespace GlobalTheory.StdSumFix

variable {D : D7}

theorem zero_mem_TT (T : Tor D) (N N' : ℕ) : (0 : VC D N N' → ℂ) ∈ TT D T N N' :=
  ⟨differentiable_const 0, 1, one_pos, fun x _ => by funext z; simp [Wd, U]⟩

theorem add_mem_TT {T : Tor D} {N N' : ℕ} {F G : VC D N N' → ℂ} (hF : F ∈ TT D T N N') (hG : G ∈ TT D T N N') :
    F + G ∈ TT D T N N' := by
  obtain ⟨hF1, m, hm, hFm⟩ := hF
  obtain ⟨hG1, n, hn, hGn⟩ := hG
  refine ⟨hF1.add hG1, m * n, Nat.mul_pos hm hn, fun x hx => ?_⟩
  have h1 := hFm (n • x) (AddSubgroup.nsmul_mem _ hx n)
  have h2 := hGn (m • x) (AddSubgroup.nsmul_mem _ hx m)
  rw [smul_smul] at h1 h2
  rw [mul_comm n m] at h2
  funext z
  have e1 := congrFun h1 z
  have e2 := congrFun h2 z
  simp only [Wd, U, Pi.add_apply] at e1 e2 ⊢
  linear_combination e1 + e2

theorem Om_sum {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {e0 : VC D N N' → ℂ} (W : WeilO D cc δ N N' e0)
    (g : GA D N) (g' : GA D N') {ι : Type*} (s : Finset ι) (f : ι → VC D N N' → ℂ)
    (hf : ∀ i ∈ s, f i ∈ TT D (tor0 D cc δ) N N') :
    (∑ i ∈ s, f i) ∈ TT D (tor0 D cc δ) N N' ∧ W.Om g g' (∑ i ∈ s, f i) = ∑ i ∈ s, W.Om g g' (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using zero_mem_TT (tor0 D cc δ) N N', ?_⟩
    have h := W.smul g g' 0 0 (zero_mem_TT _ N N')
    simpa using h
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hfi := hf i (Finset.mem_insert_self i s)
    obtain ⟨h1, h2⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    exact ⟨add_mem_TT hfi h1, by rw [W.add g g' _ hfi _ h1, h2]⟩

end GlobalTheory.StdSumFix

namespace GlobalTheory.StdSumFix

variable {D : D7}

section Reps

variable {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) {𝔪 : Ideal (𝓞 D.host.E)}
  {v : VC D a d → ℂ} {R : Finset (GA D a)}

theorem Om_rep (hv : v ∈ TT D (tor0 D ⊤ δ) a d) (hfix : ∀ k ∈ intG D a, CongOne D 𝔪 k → W.Om k 1 v = v)
    {x r : GA D a} (hx : x ∈ intG D a) (hr : r ∈ intG D a) (hc : CongOne D 𝔪 (r⁻¹ * x)) :
    W.Om x 1 v = W.Om r 1 v := by
  have h := W.mul r (r⁻¹ * x) 1 1 v hv
  rw [mul_inv_cancel_left, mul_one] at h
  rw [h, hfix _ (mul_mem (inv_mem hr) hx) hc]

theorem sum_reindex (hv : v ∈ TT D (tor0 D ⊤ δ) a d) (hfix : ∀ k ∈ intG D a, CongOne D 𝔪 k → W.Om k 1 v = v)
    (hRi : ∀ r ∈ R, r ∈ intG D a) (hR : ∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k))
    (φ : GA D a → GA D a) (hφ : ∀ r ∈ R, φ r ∈ intG D a)
    (inj : ∀ r₁ ∈ R, ∀ r₂ ∈ R, ∀ s ∈ R, CongOne D 𝔪 (s⁻¹ * φ r₁) → CongOne D 𝔪 (s⁻¹ * φ r₂) → r₁ = r₂)
    (surj : ∀ s ∈ R, ∃ r ∈ R, CongOne D 𝔪 (s⁻¹ * φ r)) :
    ∑ r ∈ R, W.Om (φ r) 1 v = ∑ s ∈ R, W.Om s 1 v := by
  classical
  let ψ : GA D a → GA D a := fun r => if h : r ∈ R then (hR (φ r) (hφ r h)).exists.choose else r
  have hψ : ∀ r ∈ R, ψ r ∈ R ∧ CongOne D 𝔪 ((ψ r)⁻¹ * φ r) := fun r hr => by
    simp only [ψ, dif_pos hr]; exact (hR (φ r) (hφ r hr)).exists.choose_spec
  refine Finset.sum_nbij ψ (fun r hr => (hψ r hr).1) ?_ ?_ ?_
  · intro r₁ hr₁ r₂ hr₂ e
    have h1 := (hψ r₁ hr₁).2
    have h2 := (hψ r₂ hr₂).2
    rw [e] at h1
    exact inj r₁ hr₁ r₂ hr₂ (ψ r₂) (hψ r₂ hr₂).1 h1 h2
  · intro s hs
    obtain ⟨r, hr, hc⟩ := surj s hs
    exact ⟨r, hr, (hR (φ r) (hφ r hr)).unique (hψ r hr) ⟨hs, hc⟩⟩
  · intro r hr
    exact Om_rep W hv hfix (hφ r hr) (hRi _ (hψ r hr).1) (hψ r hr).2

end Reps

theorem stdSum_fix_eig : ∀ (D : D7) (δ : ℂ) (a d : ℕ) (e0 : VC D a d → ℂ) (W : WeilO D ⊤ δ a d e0)
    (𝔪 : Ideal (𝓞 D.host.E)) (v : VC D a d → ℂ), v ∈ TT D (tor0 D ⊤ δ) a d →
    (∀ k ∈ intG D a, CongOne D 𝔪 k → W.Om k 1 v = v) → ∀ R : Finset (GA D a), (∀ r ∈ R, r ∈ intG D a) →
    (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) →
    (∀ k ∈ intG D a, W.Om k 1 (∑ r ∈ R, W.Om r 1 v) = ∑ r ∈ R, W.Om r 1 v) ∧
    ∀ (j : GA D d) (k : GA D a) (c : ℂ), k ∈ intG D a → W.Om 1 j v = c • W.Om k 1 v →
      W.Om 1 j (∑ r ∈ R, W.Om r 1 v) = c • ∑ r ∈ R, W.Om r 1 v := by
  intro D δ a d e0 W 𝔪 v hv hfix R hRi hR
  have hTT : ∀ r ∈ R, W.Om r 1 v ∈ TT D (tor0 D ⊤ δ) a d := fun r _ => W.maps r 1 v hv
  have uniq : ∀ r₁ ∈ R, ∀ r₂ ∈ R, CongOne D 𝔪 (r₁⁻¹ * r₂) → r₁ = r₂ := fun r₁ h₁ r₂ h₂ hc =>
    (hR r₂ (hRi r₂ h₂)).unique ⟨h₁, hc⟩ ⟨h₂, by rw [inv_mul_cancel]; exact congOne_one⟩
  refine ⟨fun k hk => ?_, fun j k c hk hj => ?_⟩
  · rw [(Om_sum W k 1 R _ hTT).2]
    have e : ∀ r ∈ R, W.Om k 1 (W.Om r 1 v) = W.Om (k * r) 1 v := fun r _ => by
      rw [← W.mul k r 1 1 v hv, mul_one]
    rw [Finset.sum_congr rfl e]
    refine sum_reindex W hv hfix hRi hR (fun r => k * r) (fun r hr => mul_mem hk (hRi r hr)) ?_ ?_
    · intro r₁ h₁ r₂ h₂ s hs c₁ c₂
      have hm : s⁻¹ * (k * r₁) ∈ intG D a := mul_mem (inv_mem (hRi s hs)) (mul_mem hk (hRi r₁ h₁))
      have h := congOne_mul (inv_mem hm) (congOne_inv hm c₁) c₂
      have e' : (s⁻¹ * (k * r₁))⁻¹ * (s⁻¹ * (k * r₂)) = r₁⁻¹ * r₂ := by group
      rw [e'] at h
      exact uniq r₁ h₁ r₂ h₂ h
    · intro s hs
      obtain ⟨r, ⟨hr, hc⟩, -⟩ := hR (k⁻¹ * s) (mul_mem (inv_mem hk) (hRi s hs))
      refine ⟨r, hr, ?_⟩
      have h := congOne_inv (mul_mem (inv_mem (hRi r hr)) (mul_mem (inv_mem hk) (hRi s hs))) hc
      have e' : (r⁻¹ * (k⁻¹ * s))⁻¹ = s⁻¹ * (k * r) := by group
      rwa [e'] at h
  · rw [(Om_sum W 1 j R _ hTT).2]
    have e : ∀ r ∈ R, W.Om 1 j (W.Om r 1 v) = c • W.Om (r * k) 1 v := fun r _ => by
      rw [← W.mul 1 r j 1 v hv, one_mul, mul_one,
        show W.Om r j v = W.Om (r * 1) (1 * j) v by rw [mul_one, one_mul], W.mul r 1 1 j v hv, hj,
        W.smul r 1 c _ (W.maps k 1 v hv), ← W.mul r k 1 1 v hv, mul_one]
    rw [Finset.sum_congr rfl e, ← Finset.smul_sum]
    congr 1
    refine sum_reindex W hv hfix hRi hR (fun r => r * k) (fun r hr => mul_mem (hRi r hr) hk) ?_ ?_
    · intro r₁ h₁ r₂ h₂ s hs c₁ c₂
      have hm₂ : s⁻¹ * (r₂ * k) ∈ intG D a := mul_mem (inv_mem (hRi s hs)) (mul_mem (hRi r₂ h₂) hk)
      have hm₁ : s⁻¹ * (r₁ * k) ∈ intG D a := mul_mem (inv_mem (hRi s hs)) (mul_mem (hRi r₁ h₁) hk)
      have h := congOne_conj (g := r₂⁻¹ * s) (mul_mem (inv_mem (hRi r₂ h₂)) (hRi s hs))
        (congOne_mul hm₁ c₁ (congOne_inv hm₂ c₂))
      have e' : r₂⁻¹ * s * (s⁻¹ * (r₁ * k) * (s⁻¹ * (r₂ * k))⁻¹) * (r₂⁻¹ * s)⁻¹ = r₂⁻¹ * r₁ := by group
      rw [e'] at h
      exact (uniq r₂ h₂ r₁ h₁ h).symm
    · intro s hs
      obtain ⟨r, ⟨hr, hc⟩, -⟩ := hR (s * k⁻¹) (mul_mem (hRi s hs) (inv_mem hk))
      refine ⟨r, hr, ?_⟩
      have hm : r⁻¹ * (s * k⁻¹) ∈ intG D a := mul_mem (inv_mem (hRi r hr)) (mul_mem (hRi s hs) (inv_mem hk))
      have h := congOne_conj (g := k⁻¹) (inv_mem hk) (congOne_inv hm hc)
      have e' : k⁻¹ * (r⁻¹ * (s * k⁻¹))⁻¹ * k⁻¹⁻¹ = s⁻¹ * (r * k) := by group
      rwa [e'] at h

end GlobalTheory.StdSumFix
