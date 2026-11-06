import Calderon.LocalSmoothSignedTaylorRemainder
import Calderon.CompactInverseDerivativeBounds
import Calderon.MetricCompatibleSourceJetAlgebra
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Linarith
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ConnectionError MetricVolume
  ExteriorSource.MetricCompatibleSourceJetAlgebra

theorem exists_normalized_pair_compact_finite_jet_bound
    (v1 v2 : Fin 5 → R3 → ℝ)
    (B : Fin 5 → R3 →L[ℝ] R3 →L[ℝ] ℝ)
    (r : ℝ) (hr : 0 < r)
    (hv1 : ∀ k : Fin 5, ContDiffOn ℝ ∞ (v1 k) (ball (0 : R3) r))
    (hv2 : ∀ k : Fin 5, ContDiffOn ℝ ∞ (v2 k) (ball (0 : R3) r))
    (hJets1 : ∀ k : Fin 5, v1 k 0 = 0 ∧ fderiv ℝ (v1 k) 0 = 0 ∧
      fderiv ℝ (fderiv ℝ (v1 k)) 0 = B k)
    (hJets2 : ∀ k : Fin 5, v2 k 0 = 0 ∧ fderiv ℝ (v2 k) 0 = 0 ∧
      fderiv ℝ (fderiv ℝ (v2 k)) 0 = B k)
    (K : Set R3) (hK : IsCompact K) (N : ℕ) :
    let R1 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
      secondTaylorRemainder (fun t : ℝ => v1 k (t • z.1)) z.2
    let R2 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
      secondTaylorRemainder (fun t : ℝ => v2 k (t • z.1)) z.2
    ∃ (lam0 C : ℝ) (U : Set (R3 × ℝ)),
      0 < lam0 ∧ lam0 ≤ 1 ∧ 0 ≤ C ∧ IsOpen U ∧
      (K ×ˢ Icc (-lam0) lam0 ⊆ U) ∧
      (∀ z ∈ U, z.2 • z.1 ∈ ball (0 : R3) (r / 2)) ∧
      (∀ k : Fin 5, ContDiffOn ℝ ∞ (R1 k) U) ∧
      (∀ k : Fin 5, ContDiffOn ℝ ∞ (R2 k) U) ∧
      (∀ k : Fin 5, ∀ z ∈ U, z.2 ≠ 0 →
        R1 k z = (z.2 ^ 2)⁻¹ * v1 k (z.2 • z.1)) ∧
      (∀ k : Fin 5, ∀ z ∈ U, z.2 ≠ 0 →
        R2 k z = (z.2 ^ 2)⁻¹ * v2 k (z.2 • z.1)) ∧
      (∀ k : Fin 5, ∀ y : R3,
        R1 k (y, 0) = (1 / 2 : ℝ) *
          B k y y ∧
        R2 k (y, 0) = (1 / 2 : ℝ) *
          B k y y) ∧
      (∀ k : Fin 5, ∀ n : ℕ, n ≤ N → ∀ z ∈ K ×ˢ Icc (-lam0) lam0,
        ‖iteratedFDeriv ℝ n (R1 k) z‖ ≤ C) ∧
      (∀ k : Fin 5, ∀ n : ℕ, n ≤ N → ∀ z ∈ K ×ˢ Icc (-lam0) lam0,
        ‖iteratedFDeriv ℝ n (R2 k) z‖ ≤ C) ∧
      (∀ k : Fin 5, ∀ lam ∈ Icc (-lam0) lam0, ∀ n : ℕ, n ≤ N →
        ∀ y ∈ K, ‖iteratedFDeriv ℝ n (fun x => R1 k (x, lam)) y‖ ≤ C) ∧
      (∀ k : Fin 5, ∀ lam ∈ Icc (-lam0) lam0, ∀ n : ℕ, n ≤ N →
        ∀ y ∈ K, ‖iteratedFDeriv ℝ n (fun x => R2 k (x, lam)) y‖ ≤ C) := by
  classical
  let R1 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
    secondTaylorRemainder (fun t : ℝ => v1 k (t • z.1)) z.2
  let R2 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
    secondTaylorRemainder (fun t : ℝ => v2 k (t • z.1)) z.2
  let scale : (R3 × ℝ) → R3 := fun z => z.2 • z.1
  let U : Set (R3 × ℝ) := scale ⁻¹' ball (0 : R3) (r / 2)
  have hScale : ContDiff ℝ ∞ scale := contDiff_snd.smul contDiff_fst
  have hU : IsOpen U := isOpen_ball.preimage hScale.continuous
  have hScaleRoom : MapsTo scale U (ball (0 : R3) r) :=
    fun z hz => (ball_subset_ball (by linarith : r / 2 ≤ r)) hz
  have hSegment (z : R3 × ℝ) (hz : z ∈ U) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
      (z.1, a * z.2) ∈ U := by
    have hzNorm : ‖z.2 • z.1‖ < r / 2 := by simpa [U, scale] using hz
    change (a * z.2) • z.1 ∈ ball (0 : R3) (r / 2)
    rw [mem_ball_zero_iff, mul_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ha.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ha.2) hzNorm
  have hRLocal (f : R3 → ℝ) (hf : ContDiffOn ℝ ∞ f (ball (0 : R3) r)) :
      ContDiffOn ℝ ∞
        (fun z : R3 × ℝ => secondTaylorRemainder (fun t : ℝ => f (t • z.1)) z.2) U := by
    have hF : ContDiffOn ℝ ∞ (fun z : R3 × ℝ => f (z.2 • z.1)) U :=
      hf.comp hScale.contDiffOn hScaleRoom
    intro z hz
    exact (contDiffAt_secondTaylorRemainder_joint_of_open_segment
      (fun z : R3 × ℝ => f (z.2 • z.1)) U hU hF z.1 z.2
      (fun a ha => hSegment z hz a ha)).contDiffWithinAt
  have hR1 (k : Fin 5) : ContDiffOn ℝ ∞ (R1 k) U := hRLocal (v1 k) (hv1 k)
  have hR2 (k : Fin 5) : ContDiffOn ℝ ∞ (R2 k) U := hRLocal (v2 k) (hv2 k)
  have hLine (y : R3) (t : ℝ) : HasDerivAt (fun a : ℝ => a • y) y t := by
    simpa using (hasDerivAt_id t).smul_const y
  have hCurve (f : R3 → ℝ) (hf : ContDiffOn ℝ ∞ f (ball (0 : R3) r))
      (y : R3) (t : ℝ) (ht : t • y ∈ ball (0 : R3) r) :
      HasDerivAt (fun a : ℝ => f (a • y)) (fderiv ℝ f (t • y) y) t := by
    simpa only [Function.comp_def] using
      ((hf.contDiffAt (isOpen_ball.mem_nhds ht)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
        t (hLine y t)
  have hOrigin : (0 : R3) ∈ ball (0 : R3) r := by simpa using hr
  have hCurveSecond (f : R3 → ℝ)
      (hf : ContDiffOn ℝ ∞ f (ball (0 : R3) r)) (y : R3) :
      deriv (deriv (fun t : ℝ => f (t • y))) 0 =
        fderiv ℝ (fderiv ℝ f) 0 y y := by
    have hNear : ∀ᶠ t : ℝ in 𝓝 0, t • y ∈ ball (0 : R3) r :=
      (isOpen_ball.preimage (by fun_prop)).mem_nhds (by simpa using hOrigin)
    have hEq : deriv (fun t : ℝ => f (t • y)) =ᶠ[𝓝 0]
        (fun t : ℝ => fderiv ℝ f (t • y) y) := by
      filter_upwards [hNear] with t ht
      exact (hCurve f hf y t ht).deriv
    have hDf : ContDiffAt ℝ ∞ (fderiv ℝ f) 0 :=
      (hf.fderiv_of_isOpen (m := (∞ : ℕ∞ω)) isOpen_ball (by simp)).contDiffAt
        (isOpen_ball.mem_nhds hOrigin)
    have hDfLine : HasFDerivAt (fderiv ℝ f)
        (fderiv ℝ (fderiv ℝ f) (0 : R3)) ((0 : ℝ) • y) := by
      simpa only [zero_smul] using (hDf.differentiableAt (by simp)).hasFDerivAt
    have hD : HasDerivAt (fun t : ℝ => fderiv ℝ f (t • y))
        (fderiv ℝ (fderiv ℝ f) 0 y) 0 := by
      simpa only [Function.comp_def] using hDfLine.comp_hasDerivAt 0 (hLine y 0)
    calc
      deriv (deriv (fun t : ℝ => f (t • y))) 0 =
          deriv (fun t : ℝ => fderiv ℝ f (t • y) y) 0 := hEq.deriv_eq
      _ = fderiv ℝ (fderiv ℝ f) 0 y y := by
        simpa using (hD.clm_apply (hasDerivAt_const (0 : ℝ) y)).deriv
  have hNormalization (f : R3 → ℝ)
      (hf : ContDiffOn ℝ ∞ f (ball (0 : R3) r))
      (hf0 : f 0 = 0) (hDf0 : fderiv ℝ f 0 = 0)
      (z : R3 × ℝ) (hz : z ∈ U) (ht : z.2 ≠ 0) :
      secondTaylorRemainder (fun t : ℝ => f (t • z.1)) z.2 =
        (z.2 ^ 2)⁻¹ * f (z.2 • z.1) := by
    have hSigned (a : ℝ) (ha : a ∈ uIcc (0 : ℝ) z.2) :
        a • z.1 ∈ ball (0 : R3) r := by
      have hAbs : |a| ≤ |z.2| := by
        rcases le_total (0 : ℝ) z.2 with htpos | htneg
        · rw [uIcc_of_le htpos] at ha
          rw [abs_of_nonneg ha.1, abs_of_nonneg htpos]
          exact ha.2
        · rw [uIcc_of_ge htneg] at ha
          rw [abs_of_nonpos ha.2, abs_of_nonpos htneg]
          linarith [ha.1]
      have hNorm : ‖a • z.1‖ ≤ ‖z.2 • z.1‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hAbs (norm_nonneg _)
      have hzNorm : ‖z.2 • z.1‖ < r / 2 := by simpa [U, scale] using hz
      rw [mem_ball_zero_iff]
      exact lt_of_le_of_lt hNorm (lt_of_lt_of_le hzNorm (by linarith))
    have hTaylor := signed_taylor_integral_remainder
      (fun t : ℝ => f (t • z.1)) z.2 (fun a ha =>
        (hf.contDiffAt (isOpen_ball.mem_nhds (hSigned a ha))).comp a
          (by fun_prop : ContDiffAt ℝ ∞ (fun t : ℝ => t • z.1) a))
    have hD0 : deriv (fun t : ℝ => f (t • z.1)) 0 = 0 := by
      have h := (hCurve f hf z.1 0 (by simpa using hOrigin)).deriv
      simpa only [zero_smul, hDf0, _root_.zero_apply] using h
    simp only [zero_smul, hf0, hD0, smul_eq_mul, mul_zero, zero_add] at hTaylor
    have ht2 : z.2 ^ 2 ≠ 0 := pow_ne_zero 2 ht
    calc
      secondTaylorRemainder (fun t : ℝ => f (t • z.1)) z.2 =
          (z.2 ^ 2)⁻¹ * (z.2 ^ 2 *
            secondTaylorRemainder (fun t : ℝ => f (t • z.1)) z.2) := by
        rw [← mul_assoc, inv_mul_cancel₀ ht2, one_mul]
      _ = (z.2 ^ 2)⁻¹ * f (z.2 • z.1) := by rw [← hTaylor]
  have hZero1 (k : Fin 5) (y : R3) :
      R1 k (y, 0) = (1 / 2 : ℝ) *
        B k y y := by
    change secondTaylorRemainder (fun t : ℝ => v1 k (t • y)) 0 = _
    rw [secondTaylorRemainder_zero, hCurveSecond (v1 k) (hv1 k) y,
      (hJets1 k).2.2]
    rfl
  have hZero2 (k : Fin 5) (y : R3) :
      R2 k (y, 0) = (1 / 2 : ℝ) *
        B k y y := by
    change secondTaylorRemainder (fun t : ℝ => v2 k (t • y)) 0 = _
    rw [secondTaylorRemainder_zero, hCurveSecond (v2 k) (hv2 k) y,
      (hJets2 k).2.2]
    rfl
  have hZeroTube : K ×ˢ ({(0 : ℝ)} : Set ℝ) ⊆ U := by
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    have ht0 : t = 0 := mem_singleton_iff.mp ht
    subst t
    simpa [U, scale] using half_pos hr
  obtain ⟨u, w, hu, hw, hKu, h0w, hProduct⟩ :=
    generalized_tube_lemma hK isCompact_singleton hU hZeroTube
  have h0wMem : (0 : ℝ) ∈ w := h0w (by simp)
  have hwNhds : w ∈ 𝓝 (0 : ℝ) := hw.mem_nhds h0wMem
  obtain ⟨d, hd, hdw⟩ := (Metric.mem_nhds_iff (x := (0 : ℝ))).mp hwNhds
  let lam0 : ℝ := min 1 (d / 2)
  have hLam0 : 0 < lam0 := lt_min zero_lt_one (half_pos hd)
  have hLam1 : lam0 ≤ 1 := min_le_left _ _
  have hLamd : lam0 ≤ d / 2 := min_le_right _ _
  let Q : Set (R3 × ℝ) := K ×ˢ Icc (-lam0) lam0
  have hTube : Q ⊆ U := by
    intro z hz
    apply hProduct
    refine ⟨hKu hz.1, hdw ?_⟩
    have hAbs : |z.2| ≤ lam0 := abs_le.mpr hz.2
    have hLt : |z.2| < d := lt_of_le_of_lt hAbs (by linarith)
    simpa only [mem_ball_zero_iff, Real.norm_eq_abs] using hLt
  have hCompact : IsCompact Q := hK.prod isCompact_Icc
  have b1 (k : Fin 5) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, n ≤ N → ∀ z ∈ Q, ‖iteratedFDeriv ℝ n (R1 k) z‖ ≤ C :=
    exists_compact_iteratedFDeriv_bound (R1 k) Q hCompact
      (fun z hz => (hR1 k).contDiffAt (hU.mem_nhds (hTube hz))) N
  have b2 (k : Fin 5) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, n ≤ N → ∀ z ∈ Q, ‖iteratedFDeriv ℝ n (R2 k) z‖ ≤ C :=
    exists_compact_iteratedFDeriv_bound (R2 k) Q hCompact
      (fun z hz => (hR2 k).contDiffAt (hU.mem_nhds (hTube hz))) N
  let c1 : Fin 5 → ℝ := fun k => Classical.choose (b1 k)
  let c2 : Fin 5 → ℝ := fun k => Classical.choose (b2 k)
  have hc1 (k : Fin 5) : 0 ≤ c1 k ∧
      ∀ n : ℕ, n ≤ N → ∀ z ∈ Q, ‖iteratedFDeriv ℝ n (R1 k) z‖ ≤ c1 k :=
    Classical.choose_spec (b1 k)
  have hc2 (k : Fin 5) : 0 ≤ c2 k ∧
      ∀ n : ℕ, n ≤ N → ∀ z ∈ Q, ‖iteratedFDeriv ℝ n (R2 k) z‖ ≤ c2 k :=
    Classical.choose_spec (b2 k)
  let C1 : ℝ := ∑ k : Fin 5, c1 k
  let C2 : ℝ := ∑ k : Fin 5, c2 k
  have hC1 : 0 ≤ C1 := Finset.sum_nonneg (fun k _ => (hc1 k).1)
  have hC2 : 0 ≤ C2 := Finset.sum_nonneg (fun k _ => (hc2 k).1)
  have hBound1 (k : Fin 5) (n : ℕ) (hn : n ≤ N) (z : R3 × ℝ) (hz : z ∈ Q) :
      ‖iteratedFDeriv ℝ n (R1 k) z‖ ≤ C1 + C2 :=
    ((hc1 k).2 n hn z hz).trans ((Finset.single_le_sum
      (fun j _ => (hc1 j).1) (Finset.mem_univ k)).trans (le_add_of_nonneg_right hC2))
  have hBound2 (k : Fin 5) (n : ℕ) (hn : n ≤ N) (z : R3 × ℝ) (hz : z ∈ Q) :
      ‖iteratedFDeriv ℝ n (R2 k) z‖ ≤ C1 + C2 :=
    ((hc2 k).2 n hn z hz).trans ((Finset.single_le_sum
      (fun j _ => (hc2 j).1) (Finset.mem_univ k)).trans (le_add_of_nonneg_left hC1))
  have hSpatial (F : R3 × ℝ → ℝ) (hF : ContDiffOn ℝ ∞ F U)
      (t : ℝ) (y : R3) (hy : (y, t) ∈ U) (n : ℕ) :
      ‖iteratedFDeriv ℝ n (fun x : R3 => F (x, t)) y‖ ≤
        ‖iteratedFDeriv ℝ n F (y, t)‖ := by
    let b : R3 × ℝ := (0, t)
    let g : R3 →ₗᵢ[ℝ] R3 × ℝ := LinearIsometry.inl ℝ R3 ℝ
    let H : (R3 × ℝ) → ℝ := fun z => F (z + b)
    let S : Set (R3 × ℝ) := (fun z => z + b) ⁻¹' U
    have hS : IsOpen S := hU.preimage (continuous_id.add continuous_const)
    have hH : ContDiffOn ℝ ∞ H S :=
      hF.comp (contDiff_id.add contDiff_const).contDiffOn (fun z hz => hz)
    let l : R3 →L[ℝ] (R3 × ℝ) := g.toContinuousLinearMap
    have hPre : IsOpen (l ⁻¹' S) := hS.preimage l.continuous
    have hg : l y ∈ S := by simpa [S, l, g, b] using hy
    have hWithin := l.iteratedFDerivWithin_comp_right (f := H) (s := S) (x := y)
      hH hS.uniqueDiffOn hPre.uniqueDiffOn hg (i := n) (by simp)
    have hLeft : iteratedFDerivWithin ℝ n (H ∘ (l : R3 → R3 × ℝ)) (l ⁻¹' S) y =
        iteratedFDeriv ℝ n (H ∘ (l : R3 → R3 × ℝ)) y :=
      (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
        (f := H ∘ (l : R3 → R3 × ℝ)) n hPre) (show y ∈ l ⁻¹' S from hg)
    have hRight : iteratedFDerivWithin ℝ n H S (l y) = iteratedFDeriv ℝ n H (l y) :=
      (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := H) n hS) hg
    rw [hLeft, hRight] at hWithin
    have hShift : iteratedFDeriv ℝ n H (l y) = iteratedFDeriv ℝ n F (y, t) := by
      simpa [H, l, g, b] using iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := F) n b (l y)
    rw [hShift] at hWithin
    have hOrd : iteratedFDeriv ℝ n (fun x : R3 => F (x, t)) y =
        (iteratedFDeriv ℝ n F (y, t)).compContinuousLinearMap
          (fun _ : Fin n => g.toContinuousLinearMap) := by
      simpa [H, Function.comp_def, l, g, b] using hWithin
    rw [hOrd]
    exact ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le _ (fun _ => g)
  refine ⟨lam0, C1 + C2, U, hLam0, hLam1, add_nonneg hC1 hC2,
    hU, hTube, ?_, hR1, hR2, ?_, ?_, ?_, hBound1, hBound2, ?_, ?_⟩
  · intro z hz
    exact hz
  · intro k z hz ht
    exact hNormalization (v1 k) (hv1 k) (hJets1 k).1 (hJets1 k).2.1 z hz ht
  · intro k z hz ht
    exact hNormalization (v2 k) (hv2 k) (hJets2 k).1 (hJets2 k).2.1 z hz ht
  · intro k y
    exact ⟨hZero1 k y, hZero2 k y⟩
  · intro k t ht n hn y hy
    exact (hSpatial (R1 k) (hR1 k) t y (hTube ⟨hy, ht⟩) n).trans
      (hBound1 k n hn (y, t) ⟨hy, ht⟩)
  · intro k t ht n hn y hy
    exact (hSpatial (R2 k) (hR2 k) t y (hTube ⟨hy, ht⟩) n).trans
      (hBound2 k n hn (y, t) ⟨hy, ht⟩)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
