import Calderon.MixedKernelConstruction.MixedKernelPhaseCompositionV021
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

open Geometry


/-! ## C2: strict phase on the literal native coordinate Hessian -/
section C4StrictPhaseNative
open scoped ContDiff Topology

/-- C2a: first derivative of `psi = theta - kappa theta^2`. -/
theorem hasFDerivAt_strictPhase {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (κ : ℝ) (y : R3) :
    HasFDerivAt (fun z => θ z - κ * θ z ^ 2) ((1 - 2 * κ * θ y) • fderiv ℝ θ y) y := by
  have hd : HasFDerivAt θ (fderiv ℝ θ y) y := (hθ.differentiable (by simp) y).hasFDerivAt
  have h2 := (hd.mul hd).const_mul κ
  convert hd.sub h2 using 1
  · funext z
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  · ext v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, smul_eq_mul]
    ring

/-- C2b: second derivative of the strict phase (any level). -/
theorem fderiv_fderiv_strictPhase_apply {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (κ : ℝ)
    (p X Y : R3) :
    fderiv ℝ (fderiv ℝ (fun z => θ z - κ * θ z ^ 2)) p X Y =
      (1 - 2 * κ * θ p) * fderiv ℝ (fderiv ℝ θ) p X Y -
        2 * κ * fderiv ℝ θ p X * fderiv ℝ θ p Y := by
  have hD : fderiv ℝ (fun z => θ z - κ * θ z ^ 2) =
      fun y => (1 - 2 * κ * θ y) • fderiv ℝ θ y :=
    funext fun y => (hasFDerivAt_strictPhase hθ κ y).fderiv
  have hd : HasFDerivAt θ (fderiv ℝ θ p) p := (hθ.differentiable (by simp) p).hasFDerivAt
  have hc : HasFDerivAt (fun y => 1 - 2 * κ * θ y) (-((2 * κ) • fderiv ℝ θ p)) p :=
    (hd.const_mul (2 * κ)).const_sub 1
  have hdd : HasFDerivAt (fderiv ℝ θ) (fderiv ℝ (fderiv ℝ θ) p) p :=
    ((hθ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) p).hasFDerivAt
  have h : HasFDerivAt (fun y => (1 - 2 * κ * θ y) • fderiv ℝ θ y)
      ((1 - 2 * κ * θ p) • fderiv ℝ (fderiv ℝ θ) p +
        (-((2 * κ) • fderiv ℝ θ p)).smulRight (fderiv ℝ θ p)) p := hc.smul hdd
  rw [hD, h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.neg_apply, smul_eq_mul]
  ring

/-- C2c: the literal native coordinate Hessian of the strict phase, for ANY `Γ`. -/
theorem coordinateHessian_strictPhase {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (κ : ℝ)
    (Γ : R3 → R3 → R3) (p X Y : R3) :
    RadiusProfile.coordinateHessian (fun z => θ z - κ * θ z ^ 2) Γ p X Y =
      (1 - 2 * κ * θ p) * RadiusProfile.coordinateHessian θ Γ p X Y -
        2 * κ * fderiv ℝ θ p X * fderiv ℝ θ p Y := by
  unfold RadiusProfile.coordinateHessian
  rw [fderiv_fderiv_strictPhase_apply hθ κ p X Y, (hasFDerivAt_strictPhase hθ κ p).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- C2d: at the zero level the strict phase has the SAME first derivative. -/
theorem fderiv_strictPhase_of_zero {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (κ : ℝ) {p : R3}
    (h0 : θ p = 0) :
    fderiv ℝ (fun z => θ z - κ * θ z ^ 2) p = fderiv ℝ θ p := by
  rw [(hasFDerivAt_strictPhase hθ κ p).fderiv, h0]
  simp

/-- C2d: zero-level two-direction strictness with the explicit `2 kappa (Dθ e)^2` loss;
a margin `c` and the budget `2 kappa (Dθ e)^2 ≤ c/2` give `c/2`. -/
theorem coordinateHessian_strictPhase_margin_of_zero {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (κ : ℝ) (Γ : R3 → R3 → R3) {p : R3} (h0 : θ p = 0) (e v : R3)
    (hv : fderiv ℝ θ p v = 0) {c : ℝ}
    (hmargin : c ≤ RadiusProfile.coordinateHessian θ Γ p e e +
      RadiusProfile.coordinateHessian θ Γ p v v)
    (hbudget : 2 * κ * (fderiv ℝ θ p e) ^ 2 ≤ c / 2) :
    c / 2 ≤ RadiusProfile.coordinateHessian (fun z => θ z - κ * θ z ^ 2) Γ p e e +
      RadiusProfile.coordinateHessian (fun z => θ z - κ * θ z ^ 2) Γ p v v := by
  rw [coordinateHessian_strictPhase hθ κ Γ p e e, coordinateHessian_strictPhase hθ κ Γ p v v,
    h0, hv]
  nlinarith only [hmargin, hbudget]

end C4StrictPhaseNative

/-! ## C3: one kappa0 for native metric-unit strictness of `psi_kappa` -/
section C4StrictPhaseUnit
open scoped ContDiff Topology InnerProductSpace
open MetricOperator ConnectionError MetricVolume

theorem exists_kappa_unitStrict_strictPhase (g : MatrixField) (p : R3) (hp : (g p).PosDef)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (h0 : θ p = 0)
    (hgrad : OAI.AnisotropicCalderon.grad θ p ≠ 0) (Gamma : R3 →L[ℝ] R3 →L[ℝ] R3)
    (hunit :
      let b : R3 := matrixOperatorMap ((g p)⁻¹)
        (WithLp.toLp 2 (OAI.AnisotropicCalderon.grad θ p))
      let e : R3 := (Real.sqrt ⟪metricOperatorField g p b, b⟫_ℝ)⁻¹ • b
      ∀ v : R3, ⟪metricOperatorField g p v, e⟫_ℝ = 0 →
        ⟪metricOperatorField g p v, v⟫_ℝ = 1 →
        0 < RadiusProfile.coordinateHessian θ (fun A B => Gamma A B) p e e +
          RadiusProfile.coordinateHessian θ (fun A B => Gamma A B) p v v) :
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ0 →
      OAI.AnisotropicCalderon.grad (fun z => θ z - κ * θ z ^ 2) p =
        OAI.AnisotropicCalderon.grad θ p ∧
      (let b : R3 := matrixOperatorMap ((g p)⁻¹)
        (WithLp.toLp 2 (OAI.AnisotropicCalderon.grad (fun z => θ z - κ * θ z ^ 2) p))
       let e : R3 := (Real.sqrt ⟪metricOperatorField g p b, b⟫_ℝ)⁻¹ • b
       ∀ v : R3, ⟪metricOperatorField g p v, e⟫_ℝ = 0 →
        ⟪metricOperatorField g p v, v⟫_ℝ = 1 →
        0 < RadiusProfile.coordinateHessian (fun z => θ z - κ * θ z ^ 2)
            (fun A B => Gamma A B) p e e +
          RadiusProfile.coordinateHessian (fun z => θ z - κ * θ z ^ 2)
            (fun A B => Gamma A B) p v v) := by
  classical
  let M : R3 →L[ℝ] R3 := metricOperatorField g p
  let b : R3 := matrixOperatorMap ((g p)⁻¹) (WithLp.toLp 2 (OAI.AnisotropicCalderon.grad θ p))
  let n : ℝ := ⟪M b, b⟫_ℝ
  let t : ℝ := (Real.sqrt n)⁻¹
  let e : R3 := t • b
  change ∀ v : R3, ⟪M v, e⟫_ℝ = 0 → ⟪M v, v⟫_ℝ = 1 →
    0 < RadiusProfile.coordinateHessian θ (fun A B => Gamma A B) p e e +
      RadiusProfile.coordinateHessian θ (fun A B => Gamma A B) p v v at hunit
  have hGA : ∀ U : R3, M (matrixOperatorMap ((g p)⁻¹) U) = U := by
    have hmat : g p * (g p)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hp.isUnit)
    have hop : matrixOperatorMap (g p) * matrixOperatorMap ((g p)⁻¹) = 1 := by
      change matrixOperatorAlgEquiv (g p) * matrixOperatorAlgEquiv ((g p)⁻¹) = 1
      rw [← map_mul, hmat, map_one]
    intro U
    change (matrixOperatorMap (g p) * matrixOperatorMap ((g p)⁻¹)) U = U
    rw [hop]
    rfl
  have hn : 0 < n := by
    change 0 < ⟪M (matrixOperatorMap ((g p)⁻¹)
      (WithLp.toLp 2 (OAI.AnisotropicCalderon.grad θ p))),
      matrixOperatorMap ((g p)⁻¹) (WithLp.toLp 2 (OAI.AnisotropicCalderon.grad θ p))⟫_ℝ
    rw [hGA]
    have h := hp.inv.dotProduct_mulVec_pos hgrad
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp,
      Pi.star_apply, star_trivial, dotProduct, Matrix.mulVec, matrixOperator_coordinate,
      PiLp.toLp_apply, mul_comm] using h
  have hGradient : ∀ Y : R3, ⟪M b, Y⟫_ℝ = fderiv ℝ θ p Y := by
    intro Y
    change ⟪M (matrixOperatorMap ((g p)⁻¹)
      (WithLp.toLp 2 (OAI.AnisotropicCalderon.grad θ p))), Y⟫_ℝ = _
    rw [hGA, covector_coordinate_sum (fderiv ℝ θ p) Y]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp,
      Pi.star_apply, star_trivial, dotProduct, OAI.AnisotropicCalderon.grad,
      OAI.AnisotropicCalderon.pd, coordinateVector]
  have hPair : ∀ X : R3, ⟪M X, b⟫_ℝ = fderiv ℝ θ p X := by
    intro X
    have hSym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hp.isHermitian
    change ⟪(g p).toEuclideanLin X, b⟫_ℝ = _
    exact ((hSym X b).trans (real_inner_comm _ _)).trans (hGradient X)
  have ht : 0 < t := inv_pos.mpr (Real.sqrt_pos.mpr hn)
  have hTan : ∀ v : R3, ⟪M v, e⟫_ℝ = 0 → fderiv ℝ θ p v = 0 := by
    intro v hv
    have h1 : ⟪M v, e⟫_ℝ = t * fderiv ℝ θ p v := by
      change ⟪M v, t • b⟫_ℝ = _
      rw [inner_smul_right, hPair]
    rw [h1] at hv
    exact (mul_eq_zero.mp hv).resolve_left ht.ne'
  -- compactness of the native unit tangent set
  have hMcont : Continuous fun v : R3 => ⟪M v, v⟫_ℝ := M.continuous.inner continuous_id
  have hPos : ∀ v : R3, v ≠ 0 → 0 < ⟪M v, v⟫_ℝ := by
    intro v hv
    have hv' : (WithLp.ofLp v : Fin 3 → ℝ) ≠ 0 := by
      intro hz
      apply hv
      ext j
      exact congrFun hz j
    have hE : ⟪M v, v⟫_ℝ = dotProduct (WithLp.ofLp v) (Matrix.mulVec (g p) (WithLp.ofLp v)) := by
      change ⟪(g p).toEuclideanLin v, v⟫_ℝ = _
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, Pi.star_apply, star_trivial,
        Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp]
    rw [hE]
    simpa only [star_trivial] using hp.dotProduct_mulVec_pos hv'
  obtain ⟨β, hβ, hβmin⟩ := (isCompact_sphere (0 : R3) 1).exists_forall_le'
    hMcont.continuousOn (fun w hw => hPos w (by
      have hnw : ‖w‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
      intro h
      simp only [h, norm_zero] at hnw
      norm_num at hnw))
  have hLower : ∀ v : R3, β * ‖v‖ ^ 2 ≤ ⟪M v, v⟫_ℝ := by
    intro v
    by_cases hv : v = 0
    · subst v
      simp
    have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let w : R3 := ‖v‖⁻¹ • v
    have hw : ‖w‖ = 1 := by
      simp only [w, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnv),
        inv_mul_cancel₀ hnv.ne']
    have hMinw := hβmin w (by simpa only [Metric.mem_sphere, dist_zero_right] using hw)
    have hBack : ‖v‖ • w = v := by
      simp only [w, smul_smul, mul_inv_cancel₀ hnv.ne', one_smul]
    have hScale : ⟪M (‖v‖ • w), ‖v‖ • w⟫_ℝ = ‖v‖ ^ 2 * ⟪M w, w⟫_ℝ := by
      simp only [map_smul, inner_smul_left, inner_smul_right, conj_trivial]
      ring
    rw [hBack] at hScale
    rw [hScale, mul_comm β (‖v‖ ^ 2)]
    exact mul_le_mul_of_nonneg_left hMinw (sq_nonneg ‖v‖)
  let K : Set R3 := {v : R3 | ⟪M v, e⟫_ℝ = 0} ∩ {v : R3 | ⟪M v, v⟫_ℝ = 1}
  have hK : IsCompact K := by
    apply Metric.isCompact_iff_isClosed_bounded.mpr
    refine ⟨?_, ?_⟩
    · exact (isClosed_eq (M.continuous.inner continuous_const) continuous_const).inter
        (isClosed_eq hMcont continuous_const)
    · apply (Metric.isBounded_closedBall (x := (0 : R3)) (r := 1 / β + 1)).subset
      intro v hv
      rw [Metric.mem_closedBall, dist_zero_right]
      have hL := hLower v
      rw [hv.2] at hL
      have hSq : ‖v‖ ^ 2 ≤ 1 / β := by
        rw [le_div_iff₀ hβ]
        nlinarith only [hL]
      nlinarith only [hSq, sq_nonneg (‖v‖ - 1 / 2)]
  have hFc : Continuous fun v : R3 =>
      RadiusProfile.coordinateHessian θ (fun A B => Gamma A B) p e e +
        RadiusProfile.coordinateHessian θ (fun A B => Gamma A B) p v v := by
    unfold RadiusProfile.coordinateHessian
    exact continuous_const.add
      (((fderiv ℝ (fderiv ℝ θ) p).continuous.clm_apply continuous_id).sub
        ((fderiv ℝ θ p).continuous.comp (Gamma.continuous.clm_apply continuous_id)))
  obtain ⟨c, hc0, hcK⟩ := exists_pos_margin_of_isCompact hK hFc.continuousOn
    (fun v hv => hunit v hv.1 hv.2)
  let d : ℝ := fderiv ℝ θ p e
  have hden : 0 < 4 * (1 + d ^ 2) := by positivity
  refine ⟨c / (4 * (1 + d ^ 2)), div_pos hc0 hden, fun κ hκ hκ0 => ?_⟩
  have hgradEq : OAI.AnisotropicCalderon.grad (fun z => θ z - κ * θ z ^ 2) p =
      OAI.AnisotropicCalderon.grad θ p := by
    funext i
    simp only [OAI.AnisotropicCalderon.grad, OAI.AnisotropicCalderon.pd,
      fderiv_strictPhase_of_zero hθ κ h0]
  refine ⟨hgradEq, ?_⟩
  rw [hgradEq]
  intro b' e'
  change ∀ v : R3, ⟪M v, e⟫_ℝ = 0 → ⟪M v, v⟫_ℝ = 1 →
    0 < RadiusProfile.coordinateHessian (fun z => θ z - κ * θ z ^ 2)
        (fun A B => Gamma A B) p e e +
      RadiusProfile.coordinateHessian (fun z => θ z - κ * θ z ^ 2)
        (fun A B => Gamma A B) p v v
  intro v hv1 hv2
  have hk : κ * (4 * (1 + d ^ 2)) ≤ c := (le_div_iff₀ hden).mp hκ0
  have hbud : 2 * κ * (fderiv ℝ θ p e) ^ 2 ≤ c / 2 := by
    change 2 * κ * d ^ 2 ≤ c / 2
    nlinarith only [hk, hκ]
  have hm := coordinateHessian_strictPhase_margin_of_zero hθ κ (fun A B => Gamma A B) h0 e v
    (hTan v hv1) (hcK v ⟨hv1, hv2⟩) hbud
  linarith

/-- C4: chain C3 → C1d. From native metric-unit strictness of `θ` (the output shape of
`exists_local_product_phase_gap`) get ONE `κ0` such that each strict phase
`θ - κ θ^2`, `0 ≤ κ ≤ κ0`, has raw Mgrad strictness for the LITERAL conformal
coefficient `h * g⁻¹` with its own field `bv`. -/
theorem exists_kappa_conformal_strict_strictPhase (g : MatrixField) (h : R3 → ℝ) (p : R3)
    (hp : (g p).PosDef) (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) p)
    (hs : ∀ᶠ y in 𝓝 p, (g y).IsHermitian)
    (hginv : ∀ i k, ContDiff ℝ ∞ (fun y => (g y)⁻¹ i k))
    (hh : ContDiff ℝ ∞ h) (hhp : 0 < h p)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (h0 : θ p = 0)
    (hgrad : OAI.AnisotropicCalderon.grad θ p ≠ 0)
    (hunit :
      let b : R3 := matrixOperatorMap ((g p)⁻¹)
        (WithLp.toLp 2 (OAI.AnisotropicCalderon.grad θ p))
      let e : R3 := (Real.sqrt ⟪metricOperatorField g p b, b⟫_ℝ)⁻¹ • b
      ∀ v : R3, ⟪metricOperatorField g p v, e⟫_ℝ = 0 →
        ⟪metricOperatorField g p v, v⟫_ℝ = 1 →
        0 < RadiusProfile.coordinateHessian θ
          (fun X Y => coordinateConnectionField
            (inverseMetricField (metricOperatorField g)) (metricOperatorField g) p X Y) p e e +
          RadiusProfile.coordinateHessian θ
          (fun X Y => coordinateConnectionField
            (inverseMetricField (metricOperatorField g)) (metricOperatorField g) p X Y) p v v) :
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ0 → ∀ ξ : Fin 3 → ℝ,
      (∑ j : Fin 3, OAI.AnisotropicCalderon.bv (fun i k y => h y * (g y)⁻¹ i k)
          (fun z => θ z - κ * θ z ^ 2) j p * ξ j) = 0 →
      OAI.AnisotropicCalderon.quad (fun i k y => h y * (g y)⁻¹ i k) p ξ =
        OAI.AnisotropicCalderon.Nf (fun i k y => h y * (g y)⁻¹ i k)
          (fun z => θ z - κ * θ z ^ 2) p →
      0 < OAI.AnisotropicCalderon.Mgrad (fun i k y => h y * (g y)⁻¹ i k)
          (OAI.AnisotropicCalderon.bv (fun i k y => h y * (g y)⁻¹ i k)
            (fun z => θ z - κ * θ z ^ 2)) p
            (OAI.AnisotropicCalderon.grad (fun z => θ z - κ * θ z ^ 2) p) +
        OAI.AnisotropicCalderon.Mgrad (fun i k y => h y * (g y)⁻¹ i k)
          (OAI.AnisotropicCalderon.bv (fun i k y => h y * (g y)⁻¹ i k)
            (fun z => θ z - κ * θ z ^ 2)) p ξ := by
  obtain ⟨κ0, hκ0, H⟩ := exists_kappa_unitStrict_strictPhase g p hp hθ h0 hgrad
    (coordinateConnectionField (inverseMetricField (metricOperatorField g))
      (metricOperatorField g) p) hunit
  refine ⟨κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨hge, hu⟩ := H κ hκ hκ'
  have hψ : ContDiff ℝ ∞ (fun z => θ z - κ * θ z ^ 2) :=
    hθ.sub (contDiff_const.mul (hθ.pow 2))
  exact strict_weight_conformal_inverseMetric_of_unitHessian g h
    (fun z => θ z - κ * θ z ^ 2) hψ hh p hginv hg hp hs (by rw [hge]; exact hgrad) hhp hu

/-- C4: ONE common kappa for two factor statements of the C3/C4 shape (`min`). -/
theorem exists_common_kappa_of_two {P Q : ℝ → Prop}
    (hP : ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ0 → P κ)
    (hQ : ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ0 → Q κ) :
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ0 → P κ ∧ Q κ := by
  obtain ⟨a, ha, hPa⟩ := hP
  obtain ⟨b, hb, hQb⟩ := hQ
  exact ⟨min a b, lt_min ha hb, fun κ h0 h1 =>
    ⟨hPa κ h0 (h1.trans (min_le_left a b)), hQb κ h0 (h1.trans (min_le_right a b))⟩⟩

end C4StrictPhaseUnit

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
