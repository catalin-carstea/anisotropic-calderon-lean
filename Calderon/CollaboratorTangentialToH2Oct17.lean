import Calderon.FixedDirichletRegularity
import Calderon.FixedSobolevCalculus
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import TauCeti.Analysis.Sobolev.TestFunctionLp
import TauCeti.Analysis.Sobolev.Wkp.SecondOrder
import TauCeti.Analysis.Sobolev.W1p.CompactSupport
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! `H²` regularity near the boundary of the unit ball from tangential regularity and the
equation (helper for task 05). -/

noncomputable section
open MeasureTheory TopologicalSpace
open scoped InnerProductSpace ContDiff Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity.TangH2
open TauCeti TauCeti.PDE EnergyBridge

/-- `L²` norm of a test function. -/
def tnorm (φ : 𝓓(ballOpens, ℝ)) : ℝ := (eLpNorm (φ : R3 → ℝ) 2 (volume : Measure R3)).toReal

lemma tnorm_nonneg (φ : 𝓓(ballOpens, ℝ)) : 0 ≤ tnorm φ := ENNReal.toReal_nonneg

/-- A functional on test functions bounded by the `L²` norm. -/
def Bdd (Λ : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ) : Prop := ∃ C : ℝ, ∀ φ, |Λ φ| ≤ C * tnorm φ

lemma bdd_zero : Bdd 0 := ⟨0, fun φ => by simp⟩

end OAI.AnisotropicCalderon.Regularity.TangH2

namespace OAI.AnisotropicCalderon.Regularity.TangH2.Bdd
open TauCeti TauCeti.PDE EnergyBridge

lemma add {Λ₁ Λ₂ : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ} (h₁ : Bdd Λ₁) (h₂ : Bdd Λ₂) : Bdd (Λ₁ + Λ₂) := by
  obtain ⟨C₁, hC₁⟩ := h₁; obtain ⟨C₂, hC₂⟩ := h₂
  refine ⟨C₁ + C₂, fun φ => ?_⟩
  simp only [LinearMap.add_apply]
  calc |Λ₁ φ + Λ₂ φ| ≤ |Λ₁ φ| + |Λ₂ φ| := abs_add_le _ _
    _ ≤ C₁ * tnorm φ + C₂ * tnorm φ := add_le_add (hC₁ φ) (hC₂ φ)
    _ = (C₁ + C₂) * tnorm φ := by ring

lemma smul {Λ : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ} (h : Bdd Λ) (c : ℝ) : Bdd (c • Λ) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨|c| * C, fun φ => ?_⟩
  simp only [LinearMap.smul_apply, smul_eq_mul, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC φ) (abs_nonneg c)

lemma neg {Λ : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ} (h : Bdd Λ) : Bdd (-Λ) := by
  have : (-Λ) = (-1 : ℝ) • Λ := (neg_one_smul ℝ Λ).symm
  rw [this]; exact h.smul _

lemma sub {Λ₁ Λ₂ : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ} (h₁ : Bdd Λ₁) (h₂ : Bdd Λ₂) : Bdd (Λ₁ - Λ₂) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

end OAI.AnisotropicCalderon.Regularity.TangH2.Bdd

namespace OAI.AnisotropicCalderon.Regularity.TangH2
open TauCeti TauCeti.PDE EnergyBridge

lemma bdd_sum {ι : Type*} (s : Finset ι) {Λ : ι → 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ}
    (h : ∀ i ∈ s, Bdd (Λ i)) : Bdd (∑ i ∈ s, Λ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bdd_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

open Classical in
/-- Multiplication of a test function by a smooth function. -/
def mulM (c : R3 → ℝ) : 𝓓(ballOpens, ℝ) →ₗ[ℝ] 𝓓(ballOpens, ℝ) :=
  if hc : ContDiff ℝ ∞ c then
    (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) hc).toLinearMap
  else 0

lemma mulM_apply {c : R3 → ℝ} (hc : ContDiff ℝ ∞ c) (φ : 𝓓(ballOpens, ℝ)) (x : R3) :
    mulM c φ x = φ x * c x := by
  simp [mulM, hc]

/-- Multiplier action on functionals. -/
def mulF (c : R3 → ℝ) (Λ : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ) : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ := Λ ∘ₗ mulM c

lemma exists_bound_on_ball {c : R3 → ℝ} (hc : Continuous c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ (ballOpens : Set R3), |c x| ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : R3) 1).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun x hx => ?_⟩
  have hx' : x ∈ Metric.closedBall (0 : R3) 1 := Metric.ball_subset_closedBall hx
  exact (hK x hx').trans (le_max_left _ _)

lemma tnorm_mulM_le {c : R3 → ℝ} (hc : ContDiff ℝ ∞ c) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x ∈ (ballOpens : Set R3), |c x| ≤ K) (φ : 𝓓(ballOpens, ℝ)) :
    tnorm (mulM c φ) ≤ K * tnorm φ := by
  unfold tnorm
  have hle : eLpNorm (mulM c φ : R3 → ℝ) 2 volume ≤
      ENNReal.ofReal K * eLpNorm (φ : R3 → ℝ) 2 volume := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (mulM c φ).continuous.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_) 2
    rw [mulM_apply hc, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_comm]
    by_cases hx : x ∈ (ballOpens : Set R3)
    · exact mul_le_mul_of_nonneg_right (hK x hx) (abs_nonneg _)
    · have : φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hmem => hx (φ.tsupport_subset hmem))
      simp [this]
  have hfin : eLpNorm (φ : R3 → ℝ) 2 volume ≠ ⊤ :=
    (φ.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2)
      φ.hasCompactSupport).eLpNorm_ne_top
  calc (eLpNorm (mulM c φ : R3 → ℝ) 2 volume).toReal
      ≤ (ENNReal.ofReal K * eLpNorm (φ : R3 → ℝ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hle
    _ = K * (eLpNorm (φ : R3 → ℝ) 2 volume).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0]

end OAI.AnisotropicCalderon.Regularity.TangH2

namespace OAI.AnisotropicCalderon.Regularity.TangH2.Bdd
open TauCeti TauCeti.PDE EnergyBridge

lemma mulc {Λ : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ} (h : Bdd Λ) {c : R3 → ℝ} (hc : ContDiff ℝ ∞ c) :
    Bdd (mulF c Λ) := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨K, hK0, hK⟩ := exists_bound_on_ball hc.continuous
  refine ⟨max C 0 * K, fun φ => ?_⟩
  simp only [TangH2.mulF, LinearMap.coe_comp, Function.comp_apply]
  calc |Λ (mulM c φ)| ≤ C * tnorm (mulM c φ) := hC _
    _ ≤ max C 0 * tnorm (mulM c φ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (tnorm_nonneg _)
    _ ≤ max C 0 * (K * tnorm φ) :=
        mul_le_mul_of_nonneg_left (tnorm_mulM_le hc hK0 hK φ) (le_max_right _ _)
    _ = max C 0 * K * tnorm φ := by ring

end OAI.AnisotropicCalderon.Regularity.TangH2.Bdd

namespace OAI.AnisotropicCalderon.Regularity.TangH2
open TauCeti TauCeti.PDE EnergyBridge

lemma mulM_ext {c d : R3 → ℝ} (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d)
    (h : ∀ x ∈ (ballOpens : Set R3), c x = d x) : mulM c = mulM d := by
  ext φ x
  rw [mulM_apply hc, mulM_apply hd]
  by_cases hx : x ∈ (ballOpens : Set R3)
  · rw [h x hx]
  · have : φ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hmem => hx (φ.tsupport_subset hmem))
    simp [this]

lemma mulF_congr {c d : R3 → ℝ} (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d)
    (h : ∀ x ∈ (ballOpens : Set R3), c x = d x) (Λ : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ) :
    mulF c Λ = mulF d Λ := by
  simp [TangH2.mulF, mulM_ext hc hd h]

lemma mulF_mulF {c d : R3 → ℝ} (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d)
    (Λ : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ) :
    mulF c (mulF d Λ) = mulF (fun x => c x * d x) Λ := by
  have hcd : ContDiff ℝ ∞ (fun x => c x * d x) := hc.mul hd
  have : mulM d ∘ₗ mulM c = mulM (fun x => c x * d x) := by
    ext φ x
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [mulM_apply hd, mulM_apply hc, mulM_apply hcd]; ring
  simp only [TangH2.mulF, LinearMap.comp_assoc, this]

lemma mulF_add_coef {c d : R3 → ℝ} (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d)
    (Λ : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ) :
    mulF (fun x => c x + d x) Λ = mulF c Λ + mulF d Λ := by
  have hcd : ContDiff ℝ ∞ (fun x => c x + d x) := hc.add hd
  have : ∀ φ, mulM (fun x => c x + d x) φ = mulM c φ + mulM d φ := by
    intro φ; ext x
    rw [mulM_apply hcd, FunLike.coe_add, Pi.add_apply, mulM_apply hc, mulM_apply hd]; ring
  ext φ
  simp [TangH2.mulF, this]

lemma mulF_sum_coef {ι : Type*} (s : Finset ι) {c : ι → R3 → ℝ}
    (hc : ∀ i, ContDiff ℝ ∞ (c i)) (Λ : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ) :
    mulF (fun x => ∑ i ∈ s, c i x) Λ = ∑ i ∈ s, mulF (c i) Λ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext φ
    have : mulM (fun _ : R3 => (∑ i ∈ (∅ : Finset ι), c i 0)) φ = 0 := by
      ext x; rw [mulM_apply contDiff_const]; simp
    simpa [TangH2.mulF] using congrArg Λ this
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [mulF_add_coef (hc a) (ContDiff.sum fun i _ => hc i), ih]

lemma mulF_add (c : R3 → ℝ) (Λ₁ Λ₂ : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ) :
    mulF c (Λ₁ + Λ₂) = mulF c Λ₁ + mulF c Λ₂ := LinearMap.add_comp _ _ _

lemma mulF_sub (c : R3 → ℝ) (Λ₁ Λ₂ : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ) :
    mulF c (Λ₁ - Λ₂) = mulF c Λ₁ - mulF c Λ₂ := LinearMap.sub_comp _ _ _

lemma mulF_sum {ι : Type*} (s : Finset ι) (c : R3 → ℝ) (Λ : ι → 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ) :
    mulF c (∑ i ∈ s, Λ i) = ∑ i ∈ s, mulF c (Λ i) := by
  ext φ; simp [TangH2.mulF, LinearMap.sum_apply]

end OAI.AnisotropicCalderon.Regularity.TangH2

namespace OAI.AnisotropicCalderon.Regularity.TangH2.Bdd
open TauCeti TauCeti.PDE EnergyBridge

lemma of_sub {Λ₁ Λ₂ : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ} (h : Bdd (Λ₁ - Λ₂)) (h₂ : Bdd Λ₂) :
    Bdd Λ₁ := by
  simpa using h.add h₂

lemma trans {Λ₁ Λ₂ Λ₃ : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ} (h₁ : Bdd (Λ₁ - Λ₂))
    (h₂ : Bdd (Λ₂ - Λ₃)) : Bdd (Λ₁ - Λ₃) := by
  simpa using h₁.add h₂

end OAI.AnisotropicCalderon.Regularity.TangH2.Bdd

namespace OAI.AnisotropicCalderon.Regularity.TangH2
open TauCeti TauCeti.PDE EnergyBridge

lemma mulF_comm {c d : R3 → ℝ} (hc : ContDiff ℝ ∞ c) (hd : ContDiff ℝ ∞ d)
    (Λ : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ) :
    mulF c (mulF d Λ) = mulF d (mulF c Λ) := by
  rw [mulF_mulF hc hd, mulF_mulF hd hc]
  congr 1; funext x; ring

lemma exists_recip {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ ∀ t, δ ≤ t → g t * t = 1 := by
  set h : ℝ → ℝ := fun t => δ / 2 + Real.smoothTransition ((t - δ / 2) / (δ / 2)) * (t - δ / 2)
    with hh
  have hpos : ∀ t, 0 < h t := by
    intro t
    simp only [hh]
    by_cases ht : t - δ / 2 ≤ 0
    · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ht (by linarith))]
      linarith
    · have := Real.smoothTransition.nonneg ((t - δ / 2) / (δ / 2))
      have : 0 ≤ Real.smoothTransition ((t - δ / 2) / (δ / 2)) * (t - δ / 2) :=
        mul_nonneg this (by linarith)
      linarith
  have hcont : ContDiff ℝ ∞ h := by
    simp only [hh]
    exact contDiff_const.add ((Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const _)).mul (contDiff_id.sub contDiff_const))
  refine ⟨fun t => (h t)⁻¹, hcont.inv fun t => (hpos t).ne', fun t ht => ?_⟩
  have : h t = t := by
    simp only [hh]
    rw [Real.smoothTransition.one_of_one_le]
    · ring
    · rw [le_div_iff₀ (by linarith)]; linarith
  simp only [this]
  exact inv_mul_cancel₀ (by linarith)

end OAI.AnisotropicCalderon.Regularity.TangH2

namespace OAI.AnisotropicCalderon.Regularity.TangH2.Bdd
open TauCeti TauCeti.PDE EnergyBridge

/-- Division by a function bounded below on the support of a localizing cutoff. -/
lemma of_mulF_of_loc {Λ : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ} {f κ : R3 → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hf : ContDiff ℝ ∞ f) (hκ : ContDiff ℝ ∞ κ)
    (hfκ : ∀ x ∈ (ballOpens : Set R3), κ x ≠ 0 → δ ≤ f x)
    (hloc : mulF κ Λ = Λ) (h : Bdd (mulF f Λ)) : Bdd Λ := by
  obtain ⟨g, hg, hgt⟩ := exists_recip hδ
  have hq : ContDiff ℝ ∞ (fun x => κ x * g (f x)) := hκ.mul (hg.comp hf)
  have : Λ = mulF (fun x => κ x * g (f x)) (mulF f Λ) := by
    rw [mulF_mulF hq hf, ← mulF_congr hκ (hq.mul hf) _ Λ, hloc]
    intro x hx
    by_cases hk : κ x = 0
    · simp [hk]
    · rw [mul_assoc, hgt _ (hfκ x hx hk), mul_one]
  rw [this]
  exact h.mulc hq

end OAI.AnisotropicCalderon.Regularity.TangH2.Bdd

namespace OAI.AnisotropicCalderon.Regularity.TangH2
open TauCeti TauCeti.PDE EnergyBridge

lemma contDiff_coord (j : Fin 3) : ContDiff ℝ ∞ (fun x : R3 => x j) :=
  (EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff

/-- The algebraic core: tangential bounds, symmetry, the equation and localization give
bounds for all second derivatives. -/
theorem bdd_of_algebra (T : Fin 3 → Fin 3 → 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ)
    (A : Fin 3 → Fin 3 → R3 → ℝ) (hA : ∀ i k, ContDiff ℝ ∞ (A i k))
    {κ : R3 → ℝ} (hκ : ContDiff ℝ ∞ κ) {δ : ℝ} (hδ : 0 < δ)
    (hα : ∀ x ∈ (ballOpens : Set R3), κ x ≠ 0 → δ ≤ ∑ i, ∑ k, A i k x * (x k * x i))
    (hr : ∀ x ∈ (ballOpens : Set R3), κ x ≠ 0 → δ ≤ ∑ j, x j * x j)
    (hsym : ∀ i k, T i k = T k i)
    (htan : ∀ i j k, Bdd (mulF (fun x => x j) (T i k) - mulF (fun x => x k) (T i j)))
    (heq : Bdd (∑ i, ∑ k, mulF (A i k) (T i k)))
    (hloc : ∀ i k, mulF κ (T i k) = T i k) : ∀ i k, Bdd (T i k) := by
  set L := ∑ j, T j j with hL
  have hX := contDiff_coord
  have hr2 : ContDiff ℝ ∞ (fun x : R3 => ∑ j, x j * x j) :=
    ContDiff.sum fun j _ => (hX j).mul (hX j)
  -- Step A
  have stepA : ∀ i, Bdd (∑ j, mulF (fun x => x j) (T i j) - mulF (fun x => x i) L) := by
    intro i
    have := bdd_sum Finset.univ fun j _ => htan j j i
    simp only [hsym _ i, Finset.sum_sub_distrib] at this
    simpa [hL, mulF_sum, hsym] using this
  -- Step B
  have stepB : ∀ i k, Bdd (mulF (fun x => ∑ j, x j * x j) (T i k) -
      mulF (fun x => x k) (mulF (fun x => x i) L)) := by
    intro i k
    have h1 : Bdd (mulF (fun x => ∑ j, x j * x j) (T i k) -
        mulF (fun x => x k) (∑ j, mulF (fun x => x j) (T i j))) := by
      have := bdd_sum Finset.univ fun j _ => (htan i j k).mulc (hX j)
      simp only [mulF_sub, Finset.sum_sub_distrib] at this
      rw [mulF_sum_coef _ (fun j => (hX j).mul (hX j)), mulF_sum]
      convert this using 2
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [mulF_mulF (hX j) (hX j)]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [mulF_comm (hX k) (hX j)]
    refine h1.trans ?_
    rw [← mulF_sub]
    exact (stepA i).mulc (hX k)
  -- Step C
  set α : R3 → ℝ := fun x => ∑ i, ∑ k, A i k x * (x k * x i) with hαdef
  have hαc : ContDiff ℝ ∞ α :=
    ContDiff.sum fun i _ => ContDiff.sum fun k _ => (hA i k).mul ((hX k).mul (hX i))
  have stepC : Bdd (mulF α L) := by
    have h1 := heq.mulc hr2
    have h2 := bdd_sum Finset.univ fun i _ => bdd_sum Finset.univ fun k _ =>
      (stepB i k).mulc (hA i k)
    have h3 : mulF α L =
        ∑ i, ∑ k, mulF (A i k) (mulF (fun x => x k) (mulF (fun x => x i) L)) := by
      rw [hαdef, mulF_sum_coef _ (fun i => ContDiff.sum fun k _ =>
        (hA i k).mul ((hX k).mul (hX i)))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mulF_sum_coef _ (fun k => (hA i k).mul ((hX k).mul (hX i)))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mulF_mulF (hX k) (hX i), mulF_mulF (hA i k) ((hX k).mul (hX i))]
    rw [h3]
    have h4 : mulF (fun x => ∑ j, x j * x j) (∑ i, ∑ k, mulF (A i k) (T i k)) =
        ∑ i, ∑ k, mulF (A i k) (mulF (fun x => ∑ j, x j * x j) (T i k)) := by
      simp only [mulF_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      rw [mulF_comm hr2 (hA i k)]
    rw [h4] at h1
    simp only [mulF_sub, Finset.sum_sub_distrib] at h2
    simpa using h1.sub h2
  -- Step D
  have hlocL : mulF κ L = L := by
    simp only [hL, mulF_sum, hloc]
  have hLb : Bdd L := Bdd.of_mulF_of_loc hδ hαc hκ hα hlocL stepC
  -- Step E
  intro i k
  refine Bdd.of_mulF_of_loc hδ hr2 hκ hr (hloc i k) ?_
  exact (stepB i k).of_sub ((hLb.mulc (hX i)).mulc (hX k))

/-! ### Concrete functionals -/

/-- The `i`th standard basis vector. -/
def e (i : Fin 3) : R3 := EuclideanSpace.single i (1 : ℝ)

lemma coord_eq_inner (y : R3) (i : Fin 3) : y i = ⟪y, e i⟫_ℝ := by
  simp [e, EuclideanSpace.inner_single_right]

/-- `φ ↦ ∫ ∂ᵢφ * w`. -/
def Tf (i : Fin 3) (w : R3 → ℝ) : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ :=
  (((TestFunction.integralAgainstBilinCLM (n := ⊤) (ContinuousLinearMap.mul ℝ ℝ)
    (volume : Measure R3) w : 𝓓(ballOpens, ℝ) →L[ℝ] ℝ)).comp
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (e i))).toLinearMap

lemma Tf_apply {w : R3 → ℝ} (hw : LocallyIntegrableOn w (ballOpens : Set R3) volume)
    (i : Fin 3) (φ : 𝓓(ballOpens, ℝ)) :
    Tf i w φ = ∫ x, lineDeriv ℝ (φ : R3 → ℝ) x (e i) * w x := by
  simp [Tf, TestFunction.integralAgainstBilinCLM_eq_integral hw]

/-- `φ ↦ ∫ φ * w`. -/
def Pf (w : R3 → ℝ) : 𝓓(ballOpens, ℝ) →ₗ[ℝ] ℝ :=
  ((TestFunction.integralAgainstBilinCLM (n := ⊤) (ContinuousLinearMap.mul ℝ ℝ)
    (volume : Measure R3) w : 𝓓(ballOpens, ℝ) →L[ℝ] ℝ)).toLinearMap

lemma Pf_apply {w : R3 → ℝ} (hw : LocallyIntegrableOn w (ballOpens : Set R3) volume)
    (φ : 𝓓(ballOpens, ℝ)) :
    Pf w φ = ∫ x, φ x * w x := by
  simp [Pf, TestFunction.integralAgainstBilinCLM_eq_integral hw]

lemma abs_setIntegral_mul_le {g : R3 → ℝ}
    (hg : MemLp g 2 ((volume : Measure R3).restrict ballOpens)) (φ : 𝓓(ballOpens, ℝ)) :
    |∫ x in (ballOpens : Set R3), φ x * g x| ≤
      (eLpNorm g 2 ((volume : Measure R3).restrict ballOpens)).toReal * tnorm φ := by
  have h1 : ∫ x in (ballOpens : Set R3), φ x * g x =
      ⟪testFunctionLp (mu := (volume : Measure R3)) 2 φ, hg.toLp g⟫_ℝ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 φ, hg.coeFn_toLp]
      with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  rw [h1]
  refine (abs_real_inner_le_norm _ _).trans (le_of_eq ?_)
  rw [Lp.norm_toLp, mul_comm]
  congr 1
  rw [← toReal_enorm]
  exact congrArg ENNReal.toReal (enorm_testFunctionLp_eq_eLpNorm 2 φ)

lemma abs_integral_mul_le {g : R3 → ℝ}
    (hg : MemLp g 2 ((volume : Measure R3).restrict ballOpens)) (φ : 𝓓(ballOpens, ℝ)) :
    |∫ x, φ x * g x| ≤
      (eLpNorm g 2 ((volume : Measure R3).restrict ballOpens)).toReal * tnorm φ := by
  have := setIntegral_smul_eq_integral_smul (μ := (volume : Measure R3)) (w := g) φ
  simp only [smul_eq_mul] at this
  rw [← this]
  exact abs_setIntegral_mul_le hg φ

lemma locallyIntegrableOn_of_memLp {g : R3 → ℝ}
    (hg : MemLp g 2 ((volume : Measure R3).restrict ballOpens)) :
    LocallyIntegrableOn g (ballOpens : Set R3) volume :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (hg.locallyIntegrable (by norm_num))

lemma bdd_Pf {g : R3 → ℝ} (hg : MemLp g 2 ((volume : Measure R3).restrict ballOpens)) :
    Bdd (Pf g) :=
  ⟨_, fun φ => by rw [Pf_apply (locallyIntegrableOn_of_memLp hg)]; exact abs_integral_mul_le hg φ⟩

lemma contDiff_fderiv_apply {c : R3 → ℝ} (hc : ContDiff ℝ ∞ c) (v : R3) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ c x v) :=
  (hc.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

lemma locallyIntegrableOn_mul {c w : R3 → ℝ} (hc : Continuous c)
    (hw : LocallyIntegrableOn w (ballOpens : Set R3) volume) :
    LocallyIntegrableOn (fun x => c x * w x) (ballOpens : Set R3) volume :=
  hw.continuousOn_mul hc.continuousOn ballOpens.isOpen.isLocallyClosed

/-- Product rule for the multiplier action on `Tf`. -/
lemma mulF_Tf {c : R3 → ℝ} (hc : ContDiff ℝ ∞ c) {w : R3 → ℝ}
    (hw : LocallyIntegrableOn w (ballOpens : Set R3) volume) (i : Fin 3) :
    mulF c (Tf i w) = Tf i (fun x => c x * w x) + mulF (fun x => fderiv ℝ c x (e i)) (Pf w) := by
  have hcw := locallyIntegrableOn_mul hc.continuous hw
  have hdc := contDiff_fderiv_apply hc (e i)
  ext φ
  simp only [TangH2.mulF, LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply]
  rw [Tf_apply hw, Tf_apply hcw, Pf_apply hw]
  have hcoe : (mulM c φ : R3 → ℝ) = fun y => φ y * c y := funext (mulM_apply hc φ)
  have hpt : ∀ x, lineDeriv ℝ (mulM c φ : R3 → ℝ) x (e i) * w x =
      lineDeriv ℝ (φ : R3 → ℝ) x (e i) * (c x * w x) +
        mulM (fun x => fderiv ℝ c x (e i)) φ x * w x := by
    intro x
    rw [hcoe, mulM_apply hdc]
    have hφx : DifferentiableAt ℝ (φ : R3 → ℝ) x := (φ.contDiff.differentiable (by simp)) x
    have hcx : DifferentiableAt ℝ c x := (hc.differentiable (by simp)) x
    have hmul : DifferentiableAt ℝ (fun y => φ y * c y) x := hφx.mul hcx
    rw [hmul.lineDeriv_eq_fderiv, hφx.lineDeriv_eq_fderiv, fderiv_fun_mul hφx hcx]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp_rw [hpt]
  have hi1 : Integrable (fun x => lineDeriv ℝ (φ : R3 → ℝ) x (e i) * (c x * w x)) volume := by
    simpa [smul_eq_mul] using integrable_lineDeriv_smul_of_locallyIntegrableOn hcw φ (e i)
  have hi2 : Integrable (fun x => mulM (fun x => fderiv ℝ c x (e i)) φ x * w x) volume := by
    simpa [smul_eq_mul] using integrable_smul_of_locallyIntegrableOn hw
      (mulM (fun x => fderiv ℝ c x (e i)) φ)
  exact integral_add hi1 hi2

lemma Tf_sub {w₁ w₂ : R3 → ℝ} (hw₁ : LocallyIntegrableOn w₁ (ballOpens : Set R3) volume)
    (hw₂ : LocallyIntegrableOn w₂ (ballOpens : Set R3) volume) (i : Fin 3) :
    Tf i (fun x => w₁ x - w₂ x) = Tf i w₁ - Tf i w₂ := by
  ext φ
  rw [LinearMap.sub_apply, Tf_apply (w := fun x => w₁ x - w₂ x) (hw₁.sub hw₂), Tf_apply hw₁, Tf_apply hw₂]
  have hi1 : Integrable (fun x => lineDeriv ℝ (φ : R3 → ℝ) x (e i) * w₁ x) volume := by
    simpa [smul_eq_mul] using integrable_lineDeriv_smul_of_locallyIntegrableOn hw₁ φ (e i)
  have hi2 : Integrable (fun x => lineDeriv ℝ (φ : R3 → ℝ) x (e i) * w₂ x) volume := by
    simpa [smul_eq_mul] using integrable_lineDeriv_smul_of_locallyIntegrableOn hw₂ φ (e i)
  rw [← integral_sub hi1 hi2]
  congr 1; funext x; ring

/-- A function with an `L²` weak gradient gives a bounded `Tf`. -/
lemma bdd_Tf_of_hasWeakFDerivOn {z : R3 → ℝ} {G : Lp R3 2 ((volume : Measure R3).restrict ballOpens)}
    (hz : HasWeakFDerivOn volume ballOpens z (fun x => innerSL ℝ (G x))) (i : Fin 3) :
    Bdd (Tf i z) := by
  have hg : MemLp (fun x => ⟪e i, G x⟫_ℝ) 2 ((volume : Measure R3).restrict ballOpens) :=
    (innerSL ℝ (e i)).comp_memLp' (Lp.memLp G)
  refine ⟨(eLpNorm (fun x => ⟪e i, G x⟫_ℝ) 2 ((volume : Measure R3).restrict ballOpens)).toReal,
    fun φ => ?_⟩
  rw [Tf_apply hz.locallyIntegrableOn]
  have := (hz (e i)).integral_lineDeriv_smul_eq_neg_integral_smul φ
  simp only [smul_eq_mul, innerSL_apply_apply] at this
  rw [this, abs_neg]
  have h2 : (fun x => φ x * ⟪G x, e i⟫_ℝ) = fun x => φ x * ⟪e i, G x⟫_ℝ := by
    funext x; rw [real_inner_comm]
  rw [h2]
  exact abs_integral_mul_le hg φ

lemma lineDeriv_lineDeriv_comm {f : R3 → ℝ} (hf : ContDiff ℝ ∞ f) (x v w : R3) :
    lineDeriv ℝ (fun y => lineDeriv ℝ f y v) x w = lineDeriv ℝ (fun y => lineDeriv ℝ f y w) x v := by
  have hd : ∀ u : R3, (fun y => lineDeriv ℝ f y u) = fun y => fderiv ℝ f y u := fun u =>
    funext fun y => ((hf.differentiable (by simp)) y).lineDeriv_eq_fderiv
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := ∞) le_rfl).differentiable (by simp)
  have key : ∀ u u' : R3, lineDeriv ℝ (fun y => fderiv ℝ f y u) x u' =
      fderiv ℝ (fderiv ℝ f) x u' u := by
    intro u u'
    have hdiff : DifferentiableAt ℝ (fun y => fderiv ℝ f y u) x :=
      (hdf x).clm_apply (differentiableAt_const u)
    rw [hdiff.lineDeriv_eq_fderiv, fderiv_clm_apply (hdf x) (differentiableAt_const u)]
    simp
  rw [hd v, hd w, key, key]
  exact ((hf.contDiffAt).isSymmSndFDerivAt (by simp)) w v

/-- Symmetry of second derivatives. -/
lemma Tf_symm {u : R3 → ℝ} {W : R3 → R3}
    (hW : HasWeakFDerivOn volume ballOpens u (fun x => innerSL ℝ (W x)))
    (hWl : ∀ k, LocallyIntegrableOn (fun x => W x k) (ballOpens : Set R3) volume) (i k : Fin 3) :
    Tf i (fun x => W x k) = Tf k (fun x => W x i) := by
  have key : ∀ i k (φ : 𝓓(ballOpens, ℝ)), Tf i (fun x => W x k) φ =
      -∫ x, lineDeriv ℝ (fun y => lineDeriv ℝ (φ : R3 → ℝ) y (e i)) x (e k) * u x := by
    intro i k φ
    rw [Tf_apply (hWl k)]
    have hcoe : ((TestFunction.lineDerivCLM ℝ (e i) φ : 𝓓(ballOpens, ℝ)) : R3 → ℝ) =
        fun y => lineDeriv ℝ (φ : R3 → ℝ) y (e i) :=
      funext fun _ => TestFunction.lineDerivCLM_apply_of_le le_top
    have := (hW (e k)).integral_lineDeriv_smul_eq_neg_integral_smul
      (TestFunction.lineDerivCLM ℝ (e i) φ : 𝓓(ballOpens, ℝ))
    rw [hcoe] at this
    simp only [smul_eq_mul, innerSL_apply_apply] at this
    rw [this, neg_neg]
    congr 1; funext x; rw [coord_eq_inner (W x) k]
  ext φ
  rw [key i k, key k i]
  have hc : ∀ x, lineDeriv ℝ (fun y => lineDeriv ℝ (φ : R3 → ℝ) y (e i)) x (e k) =
      lineDeriv ℝ (fun y => lineDeriv ℝ (φ : R3 → ℝ) y (e k)) x (e i) := fun x =>
    lineDeriv_lineDeriv_comm φ.contDiff x (e i) (e k)
  simp_rw [hc]

/-- Localization: a cutoff equal to one near the region where `w` may be nonzero. -/
lemma Tf_loc {w : R3 → ℝ} (hw : LocallyIntegrableOn w (ballOpens : Set R3) volume) (hw0 : ∀ᵐ x ∂(volume : Measure R3), ‖x‖ < 3 / 4 → w x = 0)
    (β : ContDiffBump (0 : R3)) (hβ : β.rOut < 3 / 4) (i : Fin 3) :
    mulF (fun x => 1 - β x) (Tf i w) = Tf i w := by
  have hβc : ContDiff ℝ ∞ (fun x => β x) := β.contDiff
  have hκc : ContDiff ℝ ∞ (fun x => 1 - β x) := contDiff_const.sub hβc
  ext φ
  simp only [TangH2.mulF, LinearMap.coe_comp, Function.comp_apply]
  have hsplit : φ = mulM (fun x => 1 - β x) φ + mulM (fun x => β x) φ := by
    ext x
    rw [FunLike.coe_add, Pi.add_apply, mulM_apply hκc, mulM_apply hβc]; ring
  have hzero : Tf i w (mulM (fun x => β x) φ) = 0 := by
    rw [Tf_apply hw]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hw0] with x hx
    by_cases hxr : ‖x‖ < 3 / 4
    · simp [hx hxr]
    · have hnot : x ∉ tsupport (mulM (fun x => β x) φ : R3 → ℝ) := by
        intro hmem
        have hcoe : (mulM (fun x => β x) φ : R3 → ℝ) = fun y => φ y * β y :=
          funext (mulM_apply hβc φ)
        rw [hcoe] at hmem
        have := tsupport_mul_subset_right hmem
        rw [β.tsupport_eq, Metric.mem_closedBall, dist_zero_right] at this
        linarith
      rw [Pi.zero_apply, lineDeriv_eq_zero_of_notMem_tsupport _ hnot, zero_mul]
  conv_rhs => rw [hsplit]
  rw [map_add, hzero, add_zero]

lemma gradient_coord {f : R3 → ℝ} {x : R3} (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    gradient f x i = lineDeriv ℝ f x (e i) := by
  rw [coord_eq_inner, inner_gradient_left, hf.lineDeriv_eq_fderiv]

lemma matrixBilinearForm_eq_sum (A : Matrix (Fin 3) (Fin 3) ℝ) (η ξ : R3) :
    matrixBilinearForm A η ξ = ∑ i, ∑ k, η i * (A i k * ξ k) := by
  rw [matrixBilinearForm_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]

lemma contDiff_entry {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a) (i k : Fin 3) :
    ContDiff ℝ ∞ (fun x => a x i k) :=
  contDiff_pi.1 (contDiff_pi.1 ha i) k

/-- The equation bounds the combination `∑ aᵢₖ ∂ᵢ∂ₖ v`. -/
lemma bdd_eq {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} (ha : ContDiff ℝ ∞ a) {W : R3 → R3}
    (hWL2 : ∀ k, MemLp (fun x => W x k) 2 ((volume : Measure R3).restrict ballOpens))
    {F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)}
    (heq : ∀ φ : 𝓓(ballOpens, ℝ),
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x) (W x) =
        ∫ x in (ballOpens : Set R3), F x * φ x) :
    Bdd (∑ i, ∑ k, mulF (fun x => a x i k) (Tf i (fun x => W x k))) := by
  have hWl : ∀ k, LocallyIntegrableOn (fun x => W x k) (ballOpens : Set R3) volume :=
    fun k => locallyIntegrableOn_of_memLp (hWL2 k)
  have hA := contDiff_entry ha
  have hsplit : (∑ i, ∑ k, mulF (fun x => a x i k) (Tf i (fun x => W x k))) =
      (∑ i, ∑ k, Tf i (fun x => a x i k * W x k)) +
        ∑ i, ∑ k, mulF (fun x => fderiv ℝ (fun y => a y i k) x (e i)) (Pf (fun x => W x k)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => mulF_Tf (hA i k) (hWl k) i
  rw [hsplit]
  refine Bdd.add ?_ (bdd_sum _ fun i _ => bdd_sum _ fun k _ =>
    (bdd_Pf (hWL2 k)).mulc (contDiff_fderiv_apply (hA i k) _))
  refine ⟨(eLpNorm (F : R3 → ℝ) 2 ((volume : Measure R3).restrict ballOpens)).toReal,
    fun φ => ?_⟩
  have hawl : ∀ i k, LocallyIntegrableOn (fun x => a x i k * W x k) (ballOpens : Set R3) volume :=
    fun i k => locallyIntegrableOn_mul (hA i k).continuous (hWl k)
  have hint : ∀ i k, Integrable
      (fun x => lineDeriv ℝ (φ : R3 → ℝ) x (e i) * (a x i k * W x k)) volume := fun i k => by
    simpa [smul_eq_mul] using integrable_lineDeriv_smul_of_locallyIntegrableOn (hawl i k) φ (e i)
  have hval : (∑ i, ∑ k, Tf i (fun x => a x i k * W x k)) φ =
      ∫ x in (ballOpens : Set R3), F x * φ x := by
    rw [← heq φ]
    simp only [LinearMap.sum_apply]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Tf_apply (hawl i k) i φ]
    rw [Finset.sum_congr rfl fun i _ => (integral_finsetSum _ fun k _ => hint i k).symm]
    rw [← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hint i k]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (ballOpens : Set R3))]
    · refine setIntegral_congr_fun ballOpens.isOpen.measurableSet fun x _ => ?_
      have hφx : DifferentiableAt ℝ (φ : R3 → ℝ) x := (φ.contDiff.differentiable (by simp)) x
      simp only [matrixBilinearForm_eq_sum, gradient_coord hφx]
    · intro x hx
      have hnot : x ∉ tsupport (φ : R3 → ℝ) := fun hmem => hx (φ.tsupport_subset hmem)
      simp [lineDeriv_eq_zero_of_notMem_tsupport φ hnot]
  rw [hval]
  have h2 : (fun x => F x * φ x) = fun x => φ x * F x := funext fun x => mul_comm _ _
  rw [h2]
  exact abs_setIntegral_mul_le (Lp.memLp F) φ

end OAI.AnisotropicCalderon.Regularity.TangH2

namespace OAI.AnisotropicCalderon.Regularity
open TauCeti TauCeti.PDE EnergyBridge

open TangH2 in
/-- Let `v ∈ H¹(B)` vanish on `B_{3/4}`, have all rotational derivatives
`x_j ∂_k v - x_k ∂_j v` in `H¹(B)`, and solve `-div(a ∇v) = F` weakly against test functions,
with `a` smooth and uniformly elliptic. Then `v ∈ H²(B)`. -/
theorem exists_lowerOrder_eq_of_tangential {a : R3 → Matrix (Fin 3) (Fin 3) ℝ} {lam : ℝ}
    (ha : ContDiff ℝ ∞ a) (hlam : 0 < lam)
    (hell : ∀ x ∈ (ballOpens : Set R3), ∀ ξ : R3, lam * ‖ξ‖ ^ 2 ≤ matrixBilinearForm (a x) ξ ξ)
    {F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)}
    (v : W1p (volume : Measure R3) ballOpens 2)
    (hv0 : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, ‖x‖ < 3 / 4 → W1p.value v x = 0)
    (hz : ∀ j k : Fin 3, j ≠ k → ∃ G : Lp R3 2 ((volume : Measure R3).restrict ballOpens),
      HasWeakFDerivOn volume ballOpens
        (fun x => x j * W1p.gradient v x k - x k * W1p.gradient v x j)
        (fun x => innerSL ℝ (G x)))
    (heq : ∀ φ : 𝓓(ballOpens, ℝ),
      ∫ x in (ballOpens : Set R3), matrixBilinearForm (a x) (gradient (φ : R3 → ℝ) x)
          (W1p.gradient v x) =
        ∫ x in (ballOpens : Set R3), F x * φ x) :
    ∃ U : Wkp (volume : Measure R3) ballOpens 2 2, Wkp.lowerOrder 1 U = v := by
  have hWL2 : ∀ k, MemLp (fun x => W1p.gradient v x k) 2
      ((volume : Measure R3).restrict ballOpens) := fun k =>
    (EuclideanSpace.proj k : R3 →L[ℝ] ℝ).comp_memLp' (Lp.memLp (W1p.gradient v))
  have hWl : ∀ k, LocallyIntegrableOn (fun x => W1p.gradient v x k) (ballOpens : Set R3) volume :=
    fun k => locallyIntegrableOn_of_memLp (hWL2 k)
  -- the cutoff
  let β : ContDiffBump (0 : R3) := ⟨1 / 2, 5 / 8, by norm_num, by norm_num⟩
  have hβc : ContDiff ℝ ∞ (fun x => β x) := β.contDiff
  have hκc : ContDiff ℝ ∞ (fun x => 1 - β x) := contDiff_const.sub hβc
  have hκ : ∀ x : R3, 1 - β x ≠ 0 → 1 / 4 ≤ ‖x‖ ^ 2 := by
    intro x hx
    by_contra hlt
    have hlt : ‖x‖ ^ 2 < 1 / 4 := lt_of_not_ge hlt
    have hx' : ‖x‖ ≤ 1 / 2 := by
      nlinarith [norm_nonneg x]
    apply hx
    rw [β.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_zero_right]; exact hx')]
    ring
  -- vanishing of the gradient near the origin
  have hw0 : ∀ k, ∀ᵐ x ∂(volume : Measure R3), ‖x‖ < 3 / 4 → W1p.gradient v x k = 0 := by
    let V : Opens R3 := ⟨Metric.ball 0 (3 / 4), Metric.isOpen_ball⟩
    have hV : V ≤ ballOpens := by
      intro x hx
      change x ∈ Metric.ball (0 : R3) (3 / 4) at hx
      change x ∈ Metric.ball (0 : R3) 1
      rw [Metric.mem_ball] at hx ⊢; linarith
    have hval : ∀ᵐ x ∂(volume : Measure R3).restrict (V : Set R3), W1p.value v x = 0 := by
      have h1 := ae_restrict_of_ae_restrict_of_subset (show (V : Set R3) ⊆ ballOpens from hV) hv0
      filter_upwards [h1, ae_restrict_mem (μ := (volume : Measure R3)) V.isOpen.measurableSet]
        with x hx hxV
      exact hx (by simpa [V] using hxV)
    have hg := W1p.gradient_ae_eq_zero_of_value_ae_eq_zero hV hval
    rw [ae_restrict_iff' V.isOpen.measurableSet] at hg
    intro k
    filter_upwards [hg] with x hx hxr
    rw [hx (by simpa [V] using hxr)]
    rfl
  -- the second derivative functionals
  have hB := bdd_of_algebra (fun i k => Tf i (fun x => W1p.gradient v x k))
    (fun i k x => a x i k) (contDiff_entry ha) hκc
    (δ := min (lam / 4) (1 / 4)) (lt_min (by positivity) (by norm_num))
    (fun x hx hκx => by
      have h1 := hell x hx x
      rw [matrixBilinearForm_eq_sum] at h1
      have h2 := hκ x hκx
      have h3 : ∑ i, ∑ k, x i * (a x i k * x k) = ∑ i, ∑ k, a x i k * (x k * x i) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
      rw [← h3]
      have : lam / 4 ≤ lam * ‖x‖ ^ 2 := by nlinarith
      exact (min_le_left _ _).trans (this.trans h1))
    (fun x _ hκx => by
      have h2 := hκ x hκx
      have h3 : ∑ j, x j * x j = ‖x‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Real.norm_eq_abs, sq_abs, sq]
      rw [h3]
      exact (min_le_right _ _).trans h2)
    (fun i k => Tf_symm (W1p.hasWeakFDerivOn v) hWl i k)
    (fun i j k => by
      by_cases hjk : j = k
      · subst hjk; simpa using bdd_zero
      · obtain ⟨G, hG⟩ := hz j k hjk
        rw [mulF_Tf (contDiff_coord j) (hWl k), mulF_Tf (contDiff_coord k) (hWl j),
          add_sub_add_comm,
          ← Tf_sub (locallyIntegrableOn_mul (contDiff_coord j).continuous (hWl k))
            (locallyIntegrableOn_mul (contDiff_coord k).continuous (hWl j))]
        exact (bdd_Tf_of_hasWeakFDerivOn hG i).add
          (((bdd_Pf (hWL2 k)).mulc (contDiff_fderiv_apply (contDiff_coord j) _)).sub
            ((bdd_Pf (hWL2 j)).mulc (contDiff_fderiv_apply (contDiff_coord k) _))))
    (bdd_eq ha hWL2 heq)
    (fun i k => Tf_loc (hWl k) (hw0 k) β (by norm_num [β]) i)
  -- weak second derivatives
  have hder : ∀ i k : Fin 3, ∃ g : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens),
      HasWeakLineDerivOn volume ballOpens
        (fun x => ⟪W1p.gradient v x, EuclideanSpace.basisFun (Fin 3) ℝ k⟫_ℝ) g
        (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
    intro i k
    obtain ⟨C, hC⟩ := hB i k
    have hfun : (fun x => ⟪W1p.gradient v x, EuclideanSpace.basisFun (Fin 3) ℝ k⟫_ℝ) =
        fun x => W1p.gradient v x k := by
      funext x
      rw [EuclideanSpace.basisFun_apply, coord_eq_inner]
      rfl
    rw [hfun, EuclideanSpace.basisFun_apply]
    obtain ⟨g, -, hg⟩ := exists_norm_le_hasWeakLineDerivOn_of_abs_integral_lineDeriv_mul_le
      (mu := (volume : Measure R3)) (Omega := ballOpens) (hWl k) (e i) (le_max_right C 0)
      (fun φ => by
        rw [← Tf_apply (hWl k)]
        exact (hC φ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (tnorm_nonneg φ)))
    exact ⟨g, hg⟩
  exact W1p.exists_lowerOrder_eq_of_forall_hasWeakLineDerivOn v
    (EuclideanSpace.basisFun (Fin 3) ℝ) hder

end OAI.AnisotropicCalderon.Regularity
