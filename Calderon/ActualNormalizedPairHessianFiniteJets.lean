import Calderon.ActualNormalizedPairCompactFiniteJets
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Tactic.Ring
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Distributions Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ConnectionError MetricVolume
  ExteriorSource.MetricCompatibleSourceJetAlgebra

theorem exists_normalized_pair_hessian_compact_finite_jet_bound
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
        ∀ y ∈ K, ‖iteratedFDeriv ℝ n (fun x => R2 k (x, lam)) y‖ ≤ C) ∧
      (∀ k : Fin 5, ∀ z ∈ U,
        fderiv ℝ (fderiv ℝ (fun x : R3 => R1 k (x, z.2))) z.1 =
          fderiv ℝ (fderiv ℝ (v1 k)) (z.2 • z.1)) ∧
      (∀ k : Fin 5, ∀ z ∈ U,
        fderiv ℝ (fderiv ℝ (fun x : R3 => R2 k (x, z.2))) z.1 =
          fderiv ℝ (fderiv ℝ (v2 k)) (z.2 • z.1)) ∧
      (∀ k : Fin 5, ∀ y : R3,
        fderiv ℝ (fderiv ℝ (fun x : R3 => R1 k (x, 0))) y =
          B k ∧
        fderiv ℝ (fderiv ℝ (fun x : R3 => R2 k (x, 0))) y =
          B k) := by
  classical
  let R1 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
    secondTaylorRemainder (fun t : ℝ => v1 k (t • z.1)) z.2
  let R2 : Fin 5 → (R3 × ℝ) → ℝ := fun k z =>
    secondTaylorRemainder (fun t : ℝ => v2 k (t • z.1)) z.2
  obtain ⟨lam0, C, U, hLam0, hLam1, hC, hU, hTube, hScaleRoom,
      hR1, hR2, hNorm1, hNorm2, hZero, hJoint1, hJoint2, hSpatial1, hSpatial2⟩ :=
    exists_normalized_pair_compact_finite_jet_bound
      v1 v2 B r hr hv1 hv2 hJets1 hJets2 K hK N
  have h0Ball : (0 : R3) ∈ ball (0 : R3) r := by simpa using hr
  have hBsym (k : Fin 5) (a b : R3) : B k a b = B k b a := by
    have hSym := ((hv1 k).contDiffAt (isOpen_ball.mem_nhds h0Ball)).isSymmSndFDerivAt
      (by simp)
    have hEq := hSym.eq a b
    rw [(hJets1 k).2.2] at hEq
    exact hEq
  have hQuadratic (B0 : R3 →L[ℝ] R3 →L[ℝ] ℝ)
      (hSym : ∀ a b : R3, B0 a b = B0 b a) :
      ∀ y : R3, fderiv ℝ (fderiv ℝ (fun x : R3 => (1 / 2 : ℝ) * B0 x x)) y = B0 := by
    let Q : R3 → ℝ := fun x => (1 / 2 : ℝ) * B0 x x
    have hFirst (x : R3) : HasFDerivAt Q (B0 x) x := by
      have hB0 : HasFDerivAt (B0 : R3 → R3 →L[ℝ] ℝ) B0 x := B0.hasFDerivAt
      have hId : HasFDerivAt (fun z : R3 => z) (ContinuousLinearMap.id ℝ R3) x :=
        (ContinuousLinearMap.id ℝ R3).hasFDerivAt
      have hRaw := (hB0.clm_apply hId).const_smul (1 / 2 : ℝ)
      have hDeriv : (1 / 2 : ℝ) •
          ((B0 x).comp (ContinuousLinearMap.id ℝ R3) + B0.flip x) = B0 x := by
        ext a
        simp only [_root_.smul_apply, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.flip_apply, smul_eq_mul]
        rw [hSym a x]
        ring
      rw [hDeriv] at hRaw
      exact hRaw
    have hDQ : fderiv ℝ Q = (B0 : R3 → R3 →L[ℝ] ℝ) :=
      funext (fun x => (hFirst x).fderiv)
    intro y
    change fderiv ℝ (fderiv ℝ Q) y = B0
    rw [hDQ]
    exact B0.fderiv
  have hZeroH1 (k : Fin 5) (y : R3) :
      fderiv ℝ (fderiv ℝ (fun x : R3 => R1 k (x, 0))) y = B k := by
    have hFun : (fun x : R3 => R1 k (x, 0)) =
        (fun x : R3 => (1 / 2 : ℝ) * B k x x) :=
      funext (fun x => (hZero k x).1)
    rw [hFun]
    exact hQuadratic (B k) (hBsym k) y
  have hZeroH2 (k : Fin 5) (y : R3) :
      fderiv ℝ (fderiv ℝ (fun x : R3 => R2 k (x, 0))) y = B k := by
    have hFun : (fun x : R3 => R2 k (x, 0)) =
        (fun x : R3 => (1 / 2 : ℝ) * B k x x) :=
      funext (fun x => (hZero k x).2)
    rw [hFun]
    exact hQuadratic (B k) (hBsym k) y
  have hScaledHessian (f : R3 → ℝ) (T : Set R3) (hT : IsOpen T)
      (hf : ContDiffOn ℝ ∞ f T) (t : ℝ) (ht : t ≠ 0) (y : R3) (hy : t • y ∈ T) :
      fderiv ℝ (fderiv ℝ (fun x : R3 => (t ^ 2)⁻¹ * f (t • x))) y =
        fderiv ℝ (fderiv ℝ f) (t • y) := by
    let l : R3 →L[ℝ] R3 := t • ContinuousLinearMap.id ℝ R3
    let G : R3 → ℝ := f ∘ l
    let M : Set R3 := l ⁻¹' T
    let c : ℝ →L[ℝ] ℝ := (t ^ 2)⁻¹ • ContinuousLinearMap.id ℝ ℝ
    have hM : IsOpen M := hT.preimage l.continuous
    have hly : l y ∈ T := by simpa [l] using hy
    have hyM : y ∈ M := hly
    have hG : ContDiffOn ℝ ∞ G M := hf.comp_continuousLinearMap l
    have hWithin := l.iteratedFDerivWithin_comp_right (f := f) (s := T) (x := y)
      hf hT.uniqueDiffOn hM.uniqueDiffOn hly (i := 2) (by simp)
    have hConvL : iteratedFDerivWithin ℝ 2 (f ∘ (l : R3 → R3)) M y =
        iteratedFDeriv ℝ 2 G y :=
      (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f ∘ (l : R3 → R3)) 2 hM) hyM
    have hConvR : iteratedFDerivWithin ℝ 2 f T (l y) = iteratedFDeriv ℝ 2 f (l y) :=
      (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) 2 hT) hly
    rw [hConvL, hConvR] at hWithin
    have hLeft := c.iteratedFDeriv_comp_left (f := G) (x := y)
      (hG.contDiffAt (hM.mem_nhds hyM)) (i := 2) (by simp)
    rw [hWithin] at hLeft
    have hFun : (fun x : R3 => (t ^ 2)⁻¹ * f (t • x)) = c ∘ G := by
      funext x
      simp only [Function.comp_def, c, G, l, _root_.smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [hFun]
    ext a b
    have hEval := congrArg
      (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => R3) ℝ => D ![a, b]) hLeft
    have hStep : fderiv ℝ (fderiv ℝ (c ∘ G)) y a b =
        (t ^ 2)⁻¹ * fderiv ℝ (fderiv ℝ f) (t • y) (t • a) (t • b) := by
      simpa [iteratedFDeriv_two_apply, c, l,
        ContinuousLinearMap.compContinuousMultilinearMap_coe] using hEval
    have hCancel : (t ^ 2)⁻¹ * t * t = 1 := by
      rw [mul_assoc, ← pow_two]
      exact inv_mul_cancel₀ (pow_ne_zero 2 ht)
    rw [hStep]
    simp only [map_smul, _root_.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc, hCancel, one_mul]
  have hHessian (f : R3 → ℝ) (R0 : R3 × ℝ → ℝ) (T : Set R3) (hT : IsOpen T)
      (hf : ContDiffOn ℝ ∞ f T)
      (hMaps : ∀ z ∈ U, z.2 • z.1 ∈ T)
      (hNorm : ∀ z ∈ U, z.2 ≠ 0 → R0 z = (z.2 ^ 2)⁻¹ * f (z.2 • z.1))
      (hZeroH : ∀ y : R3, fderiv ℝ (fderiv ℝ (fun x : R3 => R0 (x, 0))) y =
        fderiv ℝ (fderiv ℝ f) 0) :
      ∀ z ∈ U, fderiv ℝ (fderiv ℝ (fun x : R3 => R0 (x, z.2))) z.1 =
        fderiv ℝ (fderiv ℝ f) (z.2 • z.1) := by
    intro z hz
    rcases eq_or_ne z.2 0 with ht0 | ht0
    · simpa only [ht0, zero_smul] using hZeroH z.1
    · let Y : Set R3 := (fun x : R3 => (x, z.2)) ⁻¹' U
      have hY : IsOpen Y := hU.preimage (continuous_id.prodMk continuous_const)
      have hyY : z.1 ∈ Y := hz
      have hGerm : (fun x : R3 => R0 (x, z.2)) =ᶠ[𝓝 z.1]
          (fun x : R3 => (z.2 ^ 2)⁻¹ * f (z.2 • x)) := by
        filter_upwards [hY.mem_nhds hyY] with x hx
        exact hNorm (x, z.2) hx ht0
      have hSecond := (hGerm.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
      exact hSecond.trans (hScaledHessian f T hT hf z.2 ht0 z.1 (hMaps z hz))
  have hMaps (z : R3 × ℝ) (hz : z ∈ U) : z.2 • z.1 ∈ ball (0 : R3) r :=
    (ball_subset_ball (by linarith : r / 2 ≤ r)) (hScaleRoom z hz)
  have hH1 (k : Fin 5) : ∀ z ∈ U,
      fderiv ℝ (fderiv ℝ (fun x : R3 => R1 k (x, z.2))) z.1 =
        fderiv ℝ (fderiv ℝ (v1 k)) (z.2 • z.1) :=
    hHessian (v1 k) (R1 k) (ball (0 : R3) r) isOpen_ball (hv1 k)
      (fun z hz => hMaps z hz) (hNorm1 k)
      (fun y => (hZeroH1 k y).trans (hJets1 k).2.2.symm)
  have hH2 (k : Fin 5) : ∀ z ∈ U,
      fderiv ℝ (fderiv ℝ (fun x : R3 => R2 k (x, z.2))) z.1 =
        fderiv ℝ (fderiv ℝ (v2 k)) (z.2 • z.1) :=
    hHessian (v2 k) (R2 k) (ball (0 : R3) r) isOpen_ball (hv2 k)
      (fun z hz => hMaps z hz) (hNorm2 k)
      (fun y => (hZeroH2 k y).trans (hJets2 k).2.2.symm)
  refine ⟨lam0, C, U, hLam0, hLam1, hC, hU, hTube, hScaleRoom,
    hR1, hR2, hNorm1, hNorm2, hZero, hJoint1, hJoint2, hSpatial1, hSpatial2,
    hH1, hH2, ?_⟩
  intro k y
  exact ⟨hZeroH1 k y, hZeroH2 k y⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
