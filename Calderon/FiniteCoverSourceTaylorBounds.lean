import Calderon.ActualPacketEndpointRadiusBound
import Calderon.ActualSourceSpatialMetricJetRecovery
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Tactic.Linarith
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource ConnectionError MetricVolume MetricOperator
  ConformalDepth ReferenceWeightedApproximation DirichletFamily.DriftBootstrap
  ExteriorSource.MetricCompatibleSourceJetAlgebra

theorem exists_closedBall_contains_native_packet_endpoints
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L) :
    ∃ B : ℝ, 1 ≤ B ∧ cylinder ⊆ ball (0 : R3) B ∧
      ∀ i : Fin cover.count, ∀ lam ∈ Icc (0 : ℝ) cover.dilationCeiling,
      ∀ y ∈ cylinder ∩ (cover.packet i).centers,
      ∀ r ∈ Icc (0 : ℝ) cover.radiusCeiling,
      ∀ z ∈ closedBall (0 : R3) 1,
        packetEndpoint S L (cover.packet i) lam y r z ∈ ball (0 : R3) B := by
  classical
  obtain ⟨D, hD1, hD⟩ := exists_packetEndpoint_radius_bound S L cover
  obtain ⟨M, hM⟩ := isCompact_native_center_cylinder.exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun x : R3 => x) cylinder)
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hDR : 0 ≤ D * cover.radiusCeiling := mul_nonneg hD0 cover.radius_positive.le
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = max 1 (M + D * cover.radiusCeiling) + 1 := ⟨_, rfl⟩
  have hB1 : 1 ≤ B := by
    linarith [le_max_left (1 : ℝ) (M + D * cover.radiusCeiling)]
  have hBM : M + D * cover.radiusCeiling < B := by
    linarith [le_max_right (1 : ℝ) (M + D * cover.radiusCeiling)]
  have hCyl : cylinder ⊆ ball (0 : R3) B := by
    intro x hx
    have hMx : ‖x‖ ≤ M := hM x hx
    rw [mem_ball_zero_iff]
    linarith
  refine ⟨B, hB1, hCyl, ?_⟩
  intro i lam hLam y hy r hr z hz
  have hDisp := hD i lam hLam y hy r hr z hz
  have hMy : ‖y‖ ≤ M := hM y hy.1
  have hDr : D * r ≤ D * cover.radiusCeiling := mul_le_mul_of_nonneg_left hr.2 hD0
  have hTri := norm_le_insert' (packetEndpoint S L (cover.packet i) lam y r z) y
  rw [mem_ball_zero_iff]
  linarith

theorem exists_uniform_finite_cover_source_taylor_bound
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L) :
    ∃ B : ℝ, 1 ≤ B ∧ cylinder ⊆ ball (0 : R3) B ∧
      ∀ (f : (ℝ × R3) → ℝ) (eta A : ℝ) (U : Set (ℝ × R3)),
        0 < eta → 0 ≤ A → IsOpen U → ContDiffOn ℝ ∞ f U →
        Icc (-eta) eta ×ˢ closedBall (0 : R3) B ⊆ U →
        (∀ lam ∈ Icc (-eta) eta, ∀ x ∈ closedBall (0 : R3) B,
          ‖iteratedFDeriv ℝ 2 (fun y : R3 => f (lam,y)) x‖ ≤ A) →
        ∃ C : ℝ, 1 ≤ C ∧
          ∀ i : Fin cover.count, ∀ lam ∈ Icc (0 : ℝ) (min eta cover.dilationCeiling),
          ∀ y ∈ cylinder ∩ (cover.packet i).centers,
          ∀ r ∈ Icc (0 : ℝ) cover.radiusCeiling,
          ∀ z ∈ closedBall (0 : R3) 1,
            (∀ a ∈ Icc (0 : ℝ) 1,
              (lam, y+a • (packetEndpoint S L (cover.packet i) lam y r z-y)) ∈ U) ∧
            (lam, packetEndpoint S L (cover.packet i) lam y r z) ∈ U ∧
            |f (lam,packetEndpoint S L (cover.packet i) lam y r z) - f (lam,y) -
              fderiv ℝ (fun x : R3 => f (lam,x)) y
                (packetEndpoint S L (cover.packet i) lam y r z-y)| ≤ C*r^2 := by
  classical
  obtain ⟨B, hB1, hCyl, hEnd⟩ := exists_closedBall_contains_native_packet_endpoints S L cover
  obtain ⟨D, hD1, hD⟩ := exists_packetEndpoint_radius_bound S L cover
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  refine ⟨B, hB1, hCyl, ?_⟩
  intro f eta A U heta hA hU hf hSub hHess
  refine ⟨max 1 (A * D ^ 2), le_max_left _ _, ?_⟩
  intro i lam hLam y hy r hr z hz
  have hLamD : lam ∈ Icc (0 : ℝ) cover.dilationCeiling :=
    ⟨hLam.1, hLam.2.trans (min_le_right _ _)⟩
  have hLamEta : lam ∈ Icc (-eta) eta :=
    ⟨(neg_nonpos.mpr heta.le).trans hLam.1, hLam.2.trans (min_le_left _ _)⟩
  have hXB := hEnd i lam hLamD y hy r hr z hz
  have hXD := hD i lam hLamD y hy r hr z hz
  generalize packetEndpoint S L (cover.packet i) lam y r z = X at hXB hXD ⊢
  -- the ambient convex ball, depending only on the cover
  let s : Set R3 := closedBall (0 : R3) B
  have hs : Convex ℝ s := convex_closedBall _ _
  have hys : y ∈ s := ball_subset_closedBall (hCyl hy.1)
  have hXs : X ∈ s := ball_subset_closedBall hXB
  have hsU (w : R3) (hw : w ∈ s) : (lam, w) ∈ U := hSub ⟨hLamEta, hw⟩
  -- the smooth spatial slice on the open slice of U
  let g : R3 → ℝ := fun x => f (lam, x)
  let V : Set R3 := (fun x : R3 => (lam, x)) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.prodMk continuous_id)
  have hg : ContDiffOn ℝ ∞ g V := contDiffOn_real_prod_slice_snd f U hf lam
  have hsV : s ⊆ V := fun w hw => hsU w hw
  have hDg : ContDiffOn ℝ ∞ (fderiv ℝ g) V := hg.fderiv_of_isOpen hV (m := ∞) (by simp)
  have hDiff (w : R3) (hw : w ∈ s) : DifferentiableAt ℝ g w :=
    (hg.contDiffAt (hV.mem_nhds (hsV hw))).differentiableAt (by simp)
  have hDDiff (w : R3) (hw : w ∈ s) : DifferentiableAt ℝ (fderiv ℝ g) w :=
    (hDg.contDiffAt (hV.mem_nhds (hsV hw))).differentiableAt (by simp)
  have hHess2 (w : R3) (hw : w ∈ s) : ‖fderiv ℝ (fderiv ℝ g) w‖ ≤ A := by
    calc
      ‖fderiv ℝ (fderiv ℝ g) w‖ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ g) w‖ := by
        rw [norm_iteratedFDeriv_one]
      _ = ‖iteratedFDeriv ℝ (1 + 1) g w‖ := norm_iteratedFDeriv_fderiv
      _ ≤ A := hHess lam hLamEta w hw
  -- convex set containing the whole segment, of radius the actual displacement
  let t : Set R3 := closedBall y ‖X - y‖ ∩ s
  have ht : Convex ℝ t := (convex_closedBall _ _).inter hs
  have hyt : y ∈ t := ⟨mem_closedBall_self (norm_nonneg _), hys⟩
  have hXt : X ∈ t := ⟨mem_closedBall.mpr (dist_eq_norm X y).le, hXs⟩
  have hNear (w : R3) (hw : w ∈ t) : ‖w - y‖ ≤ ‖X - y‖ := by
    have h := hw.1
    rw [mem_closedBall, dist_eq_norm] at h
    exact h
  have hDBound (w : R3) (hw : w ∈ t) :
      ‖fderiv ℝ g w - fderiv ℝ g y‖ ≤ A * ‖X - y‖ :=
    (ht.norm_image_sub_le_of_norm_fderiv_le (fun v hv => hDDiff v hv.2)
      (fun v hv => hHess2 v hv.2) hyt hw).trans
      (mul_le_mul_of_nonneg_left (hNear w hw) hA)
  have hTaylor : ‖g X - g y - fderiv ℝ g y (X - y)‖ ≤ A * ‖X - y‖ * ‖X - y‖ :=
    ht.norm_image_sub_le_of_norm_fderiv_le' (fun v hv => hDiff v hv.2) hDBound hyt hXt
  have hDr0 : 0 ≤ D * r := mul_nonneg hD0 hr.1
  refine ⟨fun a ha => hsU _ (hs.add_smul_sub_mem hys hXs ha), hsU X hXs, ?_⟩
  calc
    |f (lam, X) - f (lam, y) - fderiv ℝ (fun x : R3 => f (lam, x)) y (X - y)|
        = ‖g X - g y - fderiv ℝ g y (X - y)‖ := (Real.norm_eq_abs _).symm
    _ ≤ A * ‖X - y‖ * ‖X - y‖ := hTaylor
    _ ≤ A * (D * r) * (D * r) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hXD hA) hXD (norm_nonneg _)
          (mul_nonneg hA hDr0)
    _ = A * D ^ 2 * r ^ 2 := by ring
    _ ≤ max 1 (A * D ^ 2) * r ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg r)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
