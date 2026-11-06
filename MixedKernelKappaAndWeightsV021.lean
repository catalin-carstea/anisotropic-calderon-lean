import MixedKernelPrincipalCarlemanV021
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section

/-! K1–K4 (REPORT.md v019 §K, written before this code): one `κ0` for the source
strictness of `ψ_κ = θ − κθ²` and the native principal Carleman on `ψ_κ`. -/
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open scoped ContDiff

/-- The source strictness functional `H(W,W)/N + H(v,v)` of `point_criterion_of_metric_strictness`
for `G = g`, `A = g⁻¹`. -/
def srcFun (g : MatrixField) (θ : R3 → ℝ) (p : R3) (v : Fin 3 → ℝ) : ℝ :=
  (∑ i, ∑ j, StrictWeightCarleman.christoffelHess (fun i j y => g y i j)
      (fun i k y => (g y)⁻¹ i k) θ p i j *
      StrictWeightCarleman.phaseField (fun i k y => (g y)⁻¹ i k) θ i p *
      StrictWeightCarleman.phaseField (fun i k y => (g y)⁻¹ i k) θ j p) /
      StrictWeightCarleman.phaseNorm (fun i k y => (g y)⁻¹ i k) θ p +
    ∑ i, ∑ j, StrictWeightCarleman.christoffelHess (fun i j y => g y i j)
      (fun i k y => (g y)⁻¹ i k) θ p i j * v i * v j

/-- The source strictness hypothesis `hsrc` of `principal_carleman_of_metric_strictness`. -/
def SrcStrict (g : MatrixField) (θ : R3 → ℝ) (p : R3) : Prop :=
  ∀ v : Fin 3 → ℝ, ∑ i, ∑ j, g p i j * v i * v j = 1 →
    ∑ i, ∑ j, g p i j * StrictWeightCarleman.phaseField (fun i k y => (g y)⁻¹ i k) θ i p * v j = 0 →
    0 < srcFun g θ p v

/-- K1–K3: one `κ0` keeping the source strictness for every `ψ_κ`, `0 ≤ κ ≤ κ0`. -/
theorem exists_kappa_srcStrict_strictPhase (g : MatrixField) (hg : IsAdmissibleMetric g)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0) (hsrc : SrcStrict g θ p) :
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ0 →
      SrcStrict g (fun z => θ z - κ * θ z ^ 2) p := by
  have hpd : ∀ κ : ℝ, ∀ k, pd k (fun z => θ z - κ * θ z ^ 2) p = pd k θ p :=
    fun κ k => pd_strictPhase_of_zero hθ κ h0 k
  have hW : ∀ κ : ℝ, ∀ i, StrictWeightCarleman.phaseField (fun i k y => (g y)⁻¹ i k)
      (fun z => θ z - κ * θ z ^ 2) i p =
      StrictWeightCarleman.phaseField (fun i k y => (g y)⁻¹ i k) θ i p := by
    intro κ i
    simp only [StrictWeightCarleman.phaseField, hpd]
  have hN : ∀ κ : ℝ, StrictWeightCarleman.phaseNorm (fun i k y => (g y)⁻¹ i k)
      (fun z => θ z - κ * θ z ^ 2) p =
      StrictWeightCarleman.phaseNorm (fun i k y => (g y)⁻¹ i k) θ p := by
    intro κ
    simp only [StrictWeightCarleman.phaseNorm, hpd]
  have hH : ∀ κ : ℝ, ∀ i j, StrictWeightCarleman.christoffelHess (fun i j y => g y i j)
      (fun i k y => (g y)⁻¹ i k) (fun z => θ z - κ * θ z ^ 2) p i j =
      StrictWeightCarleman.christoffelHess (fun i j y => g y i j)
        (fun i k y => (g y)⁻¹ i k) θ p i j - 2 * κ * pd i θ p * pd j θ p := by
    intro κ i j
    rw [christoffelHess_strictPhase _ _ hθ κ p i j, h0]
    ring
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = (∑ i, pd i θ p *
      StrictWeightCarleman.phaseField (fun i k y => (g y)⁻¹ i k) θ i p) ^ 2 /
      StrictWeightCarleman.phaseNorm (fun i k y => (g y)⁻¹ i k) θ p := ⟨_, rfl⟩
  have hF : ∀ κ : ℝ, ∀ v : Fin 3 → ℝ, srcFun g (fun z => θ z - κ * θ z ^ 2) p v =
      srcFun g θ p v - 2 * κ * E - 2 * κ * (∑ i, pd i θ p * v i) ^ 2 := by
    intro κ v
    rw [hEdef]
    simp only [srcFun, hW, hN, hH, Fin.sum_univ_three]
    ring
  -- K2: compact constraint set
  let K : Set (Fin 3 → ℝ) := {v | ∑ i, ∑ j, g p i j * v i * v j = 1 ∧
    ∑ i, ∑ j, g p i j * StrictWeightCarleman.phaseField (fun i k y => (g y)⁻¹ i k) θ i p *
      v j = 0}
  have hc1 : Continuous fun v : Fin 3 → ℝ => ∑ i, ∑ j, g p i j * v i * v j := by
    simp only [Fin.sum_univ_three]
    fun_prop
  have hc2 : Continuous fun v : Fin 3 → ℝ => ∑ i, ∑ j, g p i j *
      StrictWeightCarleman.phaseField (fun i k y => (g y)⁻¹ i k) θ i p * v j := by
    simp only [Fin.sum_univ_three]
    fun_prop
  have hclosed : IsClosed K :=
    IsClosed.inter (isClosed_eq hc1 continuous_const) (isClosed_eq hc2 continuous_const)
  have hG := hg.posDef p
  let e0 : Fin 3 → ℝ := Pi.single 0 1
  have he0 : e0 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [e0] at this
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = dotProduct e0 (Matrix.mulVec (g p) e0) := ⟨_, rfl⟩
  have hq : 0 < q := by
    rw [hqdef]
    simpa only [star_trivial] using hG.dotProduct_mulVec_pos he0
  let a : Fin 3 → ℝ := (Real.sqrt q)⁻¹ • e0
  have ha : dotProduct a (Matrix.mulVec (g p) a) = 1 := by
    simp only [a, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, ← hqdef]
    have hs := Real.sq_sqrt hq.le
    have hsq : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
    field_simp
    nlinarith [hs]
  have hsub : K ⊆ ProductHessianSeparation.metricTangentSphere (g p) 0 a := by
    intro v hv
    refine ⟨zero_dotProduct v, ?_⟩
    rw [ha, ← hv.1]
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    ring
  have hK : IsCompact K :=
    (ProductHessianSeparation.isCompact_metricTangentSphere (g p) hG 0 a).of_isClosed_subset
      hclosed hsub
  -- K3: margin and bound
  have hFc : Continuous fun v : Fin 3 → ℝ => srcFun g θ p v := by
    unfold srcFun
    simp only [Fin.sum_univ_three]
    fun_prop
  have hdc : Continuous fun v : Fin 3 → ℝ => (∑ i, pd i θ p * v i) ^ 2 := by
    simp only [Fin.sum_univ_three]
    fun_prop
  obtain ⟨c, hc, hcK⟩ := exists_pos_margin_of_isCompact hK hFc.continuousOn
    (fun v hv => hsrc v hv.1 hv.2)
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hdc.continuousOn
  have hden : 0 < 4 * (1 + |E| + |D|) := by positivity
  refine ⟨c / (4 * (1 + |E| + |D|)), div_pos hc hden, fun κ hκ hκ0 => ?_⟩
  have hk : κ * (4 * (1 + |E| + |D|)) ≤ c := (le_div_iff₀ hden).mp hκ0
  intro v hv1 hv2
  simp only [hW κ] at hv2
  have hv : v ∈ K := ⟨hv1, hv2⟩
  have hdv : (∑ i, pd i θ p * v i) ^ 2 ≤ D := by
    have h := hD v hv
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have h1 : 2 * κ * E ≤ 2 * κ * |E| := mul_le_mul_of_nonneg_left (le_abs_self E) (by linarith)
  have h2 : 2 * κ * (∑ i, pd i θ p * v i) ^ 2 ≤ 2 * κ * |D| :=
    mul_le_mul_of_nonneg_left (hdv.trans (le_abs_self D)) (by linarith)
  have h3 : 2 * κ * |E| + 2 * κ * |D| ≤ c / 2 := by
    have e : 2 * κ * |E| + 2 * κ * |D| = κ * (4 * (1 + |E| + |D|)) / 2 - 2 * κ := by ring
    rw [e]
    linarith
  rw [hF κ v]
  linarith [hcK v hv]

/-- K4: native Carleman for the literal principal coefficient on EVERY strict phase
`ψ_κ = θ − κθ²`, `0 ≤ κ ≤ κ0`, with the SAME weight phase `ψ_κ`. -/
theorem exists_kappa_principal_carleman_strictPhase (g : MatrixField) (hg : IsAdmissibleMetric g)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict g θ p) :
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 ≤ κ → κ ≤ κ0 →
      ∃ m r C τ0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ0 ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
        ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Metric.closedBall p r →
        τ * (∫ x, ∑ i, pd i (fun y => Real.exp (τ * (θ y - κ * θ y ^ 2)) * w y) x ^ 2) +
          τ ^ 3 * (∫ x, (Real.exp (τ * (θ x - κ * θ x ^ 2)) * w x) ^ 2) ≤
          C * ∫ x, Real.exp (2 * (τ * (θ x - κ * θ x ^ 2))) *
            Lop (fun i k y => EnergyBridge.principalCoefficient g y i k) w x ^ 2 := by
  obtain ⟨κ0, hκ0, H⟩ := exists_kappa_srcStrict_strictPhase g hg hθ p h0 hsrc
  refine ⟨κ0, hκ0, fun κ hκ hκ' => ?_⟩
  have hψ : ContDiff ℝ ∞ (fun z => θ z - κ * θ z ^ 2) :=
    hθ.sub (contDiff_const.mul (hθ.pow 2))
  have hdψ : (fun k => pd k (fun z => θ z - κ * θ z ^ 2) p) ≠ 0 := by
    have e : (fun k => pd k (fun z => θ z - κ * θ z ^ 2) p) = fun k => pd k θ p :=
      funext fun k => pd_strictPhase_of_zero hθ κ h0 k
    rw [e]
    exact hdθ
  exact StrictWeightCarleman.principal_carleman_of_metric_strictness g hg hψ p hdψ (H κ hκ hκ')

/-! W1–W3 (REPORT.md v020 §W, written before this code). -/

/-- W1: the weighted SQUARED inequality gives the unsquared one (τ ≥ 1). -/
theorem weighted_sq_to_unsq {τ c a b C A D S : ℝ} (hτ : 1 ≤ τ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hD : 0 ≤ D) (hS : 0 ≤ S)
    (h : τ ^ 3 * (Real.exp (2 * (τ * c)) * A ^ 2) ≤
      C * (Real.exp (2 * (τ * a)) * D ^ 2 + Real.exp (2 * (τ * b)) * S ^ 2)) :
    Real.exp (τ * c) * A ≤ Real.sqrt C * (Real.exp (τ * a) * D + Real.exp (τ * b) * S) := by
  have hsq : ∀ t : ℝ, Real.exp (2 * t) = Real.exp t ^ 2 := fun t => by
    rw [sq, ← Real.exp_add, two_mul]
  rw [hsq, hsq, hsq] at h
  have hX : 0 ≤ Real.exp (τ * c) * A := mul_nonneg (Real.exp_pos _).le hA
  have hY : 0 ≤ Real.exp (τ * a) * D := mul_nonneg (Real.exp_pos _).le hD
  have hZ : 0 ≤ Real.exp (τ * b) * S := mul_nonneg (Real.exp_pos _).le hS
  have hτ3 : 1 ≤ τ ^ 3 := one_le_pow₀ hτ
  have hnn : 0 ≤ Real.exp (τ * c) ^ 2 * A ^ 2 := by positivity
  have h1 : (Real.exp (τ * c) * A) ^ 2 ≤
      C * ((Real.exp (τ * a) * D) ^ 2 + (Real.exp (τ * b) * S) ^ 2) :=
    calc (Real.exp (τ * c) * A) ^ 2 = Real.exp (τ * c) ^ 2 * A ^ 2 := by ring
      _ ≤ τ ^ 3 * (Real.exp (τ * c) ^ 2 * A ^ 2) := le_mul_of_one_le_left hnn hτ3
      _ ≤ _ := h
      _ = _ := by ring
  have h2 : C * ((Real.exp (τ * a) * D) ^ 2 + (Real.exp (τ * b) * S) ^ 2) ≤
      (Real.sqrt C * (Real.exp (τ * a) * D + Real.exp (τ * b) * S)) ^ 2 := by
    rw [mul_pow (Real.sqrt C), Real.sq_sqrt hC]
    exact mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hY hZ]) hC
  have hR : 0 ≤ Real.sqrt C * (Real.exp (τ * a) * D + Real.exp (τ * b) * S) :=
    mul_nonneg (Real.sqrt_nonneg _) (add_nonneg hY hZ)
  have h3 := Real.sqrt_le_sqrt (h1.trans h2)
  rwa [Real.sqrt_sq hX, Real.sqrt_sq hR] at h3

/-- W1: the checked strict-height interpolation consumer fed by the SQUARED three-level
weighted inequality (the form produced by a Carleman estimate). -/
theorem strictHeight_interpolation_of_weighted_sq {κ l e C τ0 A S D : ℝ} (hκ : 0 < κ)
    (hl : 0 < l) (hκl : κ * l ≤ 1 / 4) (he : 0 ≤ e) (he4 : 4 * e < κ * l ^ 2) (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hAD : A ≤ D)
    (h : ∀ τ : ℝ, τ0 ≤ τ → τ ^ 3 * (Real.exp (2 * (τ * strictHeight κ (-e))) * A ^ 2) ≤
      C * (Real.exp (2 * (τ * strictHeight κ (-l + 3 * e))) * D ^ 2 +
        Real.exp (2 * (τ * strictHeight κ (l + 3 * e))) * S ^ 2)) :
    ∃ C' : ℝ, 0 < C' ∧
      A ≤ C' * (S ^ ((strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) /
          (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e))) *
        D ^ (1 - (strictHeight κ (-e) - strictHeight κ (-l + 3 * e)) /
          (strictHeight κ (l + 3 * e) - strictHeight κ (-l + 3 * e)))) :=
  strictHeight_interpolation_of_weighted (C := Real.sqrt C) (τ0 := max τ0 1) hκ hl hκl he he4
    (Real.sqrt_nonneg _) hA hS hAD (fun τ hτ => weighted_sq_to_unsq
      ((le_max_right _ _).trans hτ) hC hA (hA.trans hAD) hS (h τ ((le_max_left _ _).trans hτ)))

/-- W2 (scalar): the three weight heights on `[-l, l+4ε]`. -/
theorem strictPhase_height_bounds {κ l ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (hl : 4 * ε < l)
    (hκh : κ * (l + 4 * ε) < 1 / 4) :
    (∀ s, -l ≤ s → s ≤ -l + 23 * ε / 8 → strictHeight κ s ≤ strictHeight κ (-l + 3 * ε)) ∧
    (∀ s, -l ≤ s → s ≤ l + 23 * ε / 8 → strictHeight κ s ≤ strictHeight κ (l + 3 * ε)) ∧
    (∀ s, -ε ≤ s → s ≤ l + 4 * ε → strictHeight κ (-ε) ≤ strictHeight κ s) := by
  have hk4 : 0 < 4 * κ := by linarith
  have hb : l + 4 * ε < 1 / (4 * κ) := by
    rw [lt_div_iff₀ hk4]
    linarith
  have hmono := (strictPhaseProfile_strictMonoOn hκ).monotoneOn
  have hI : ∀ t, -l ≤ t → t ≤ l + 4 * ε → t ∈ Set.Icc (-(1 / (4 * κ))) (1 / (4 * κ)) :=
    fun t h1 h2 => ⟨by linarith, by linarith⟩
  refine ⟨fun s h1 h2 => ?_, fun s h1 h2 => ?_, fun s h1 h2 => ?_⟩
  · exact hmono (hI s h1 (by linarith)) (hI _ (by linarith) (by linarith)) (by linarith)
  · exact hmono (hI s h1 (by linarith)) (hI _ (by linarith) (by linarith)) (by linarith)
  · exact hmono (hI _ (by linarith) (by linarith)) (hI s (by linarith) h2) h1

/-- W2 (native): the weight `ψ = strictHeight κ ∘ θ` on the lifted collars and closure of O. -/
theorem native_weight_heights {K : Type*} [NormedAddCommGroup K]
    (e : OpenPartialHomeomorph R3 (ℝ × K)) {θ : R3 → ℝ} {P : R3 → K} {p : R3}
    (he : ∀ x, e x = (θ x, P (x - p))) {l ε R κ : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    (hl : 4 * ε < l) (hR : 0 < R) (hκh : κ * (l + 4 * ε) < 1 / 4)
    (hDt : PhaseCoordinates.closedD l ε R ⊆ e.target) :
    (∀ x ∈ e.symm '' PhaseCoordinates.transB l ε R,
      strictHeight κ (θ x) ≤ strictHeight κ (-l + 3 * ε)) ∧
    (∀ x ∈ e.symm '' (PhaseCoordinates.transT l ε R ∪ PhaseCoordinates.transL l ε R),
      strictHeight κ (θ x) ≤ strictHeight κ (l + 3 * ε)) ∧
    (∀ x ∈ e.symm '' PhaseCoordinates.closedO l ε R,
      strictHeight κ (-ε) ≤ strictHeight κ (θ x)) := by
  have hθ : ∀ y ∈ (PhaseCoordinates.closedD l ε R : Set (ℝ × K)), θ (e.symm y) = y.1 := by
    intro y hy
    have h := e.right_inv (hDt hy)
    rw [he] at h
    exact congrArg Prod.fst h
  have hD : (PhaseCoordinates.roomD l ε R : Set (ℝ × K)) ⊆ PhaseCoordinates.closedD l ε R :=
    PhaseCoordinates.roomD_subset_closedD
  have hStD : (PhaseCoordinates.closedStop l ε R : Set (ℝ × K)) ⊆
      PhaseCoordinates.closedD l ε R :=
    (PhaseCoordinates.closedStop_subset_roomD hε hl hR).trans hD
  have hSlD : (PhaseCoordinates.closedSlat l ε R : Set (ℝ × K)) ⊆
      PhaseCoordinates.closedD l ε R :=
    (PhaseCoordinates.closedSlat_subset_roomD hε hl hR).trans hD
  obtain ⟨hB, hT, hO⟩ := strictPhase_height_bounds hκ hε hl hκh
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    rw [hθ y (((PhaseCoordinates.transB_subset_roomD hε hl hR).trans hD) hy)]
    have hy' : y ∈ Set.Icc (-l + 17 * ε / 8) (-l + 23 * ε / 8) ×ˢ
        Metric.closedBall (0 : K) (3 * R / 4) := hy
    exact hB _ (by linarith [hy'.1.1]) hy'.1.2
  · rintro x ⟨y, hy, rfl⟩
    rcases hy with hy | hy
    · rw [hθ y (((PhaseCoordinates.transT_subset_roomStop hε hR).trans
        (PhaseCoordinates.roomStop_subset_closedStop.trans hStD)) hy)]
      have hy' : y ∈ Set.Icc (l + 17 * ε / 8) (l + 23 * ε / 8) ×ˢ
          Metric.closedBall (0 : K) (3 * R / 4) := hy
      exact hT _ (by linarith [hy'.1.1]) hy'.1.2
    · rw [hθ y (((PhaseCoordinates.transL_subset_roomSlat hε hR).trans
        (PhaseCoordinates.roomSlat_subset_closedSlat.trans hSlD)) hy)]
      have hy' : y ∈ Set.Icc (-l + 17 * ε / 8) (l + 23 * ε / 8) ×ˢ
          {z : K | R / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 * R / 4} := hy
      exact hT _ (by linarith [hy'.1.1]) hy'.1.2
  · rintro x ⟨y, hy, rfl⟩
    rw [hθ y (((PhaseCoordinates.closedO_subset_roomD hε hl hR).trans hD) hy)]
    have hy' : y ∈ Set.Icc (-ε) (l + 3 * ε / 2) ×ˢ Metric.closedBall (0 : K) (R / 2) := hy
    exact hO _ hy'.1.1 (by linarith [hy'.1.2])

/-- W3: the chart centre. -/
theorem chart_symm_zero {K : Type*} [NormedAddCommGroup K]
    (e : OpenPartialHomeomorph R3 (ℝ × K)) {θ : R3 → ℝ} {P : R3 → K} {p : R3}
    (he : ∀ x, e x = (θ x, P (x - p))) (hP0 : P 0 = 0) (h0 : θ p = 0) (hpe : p ∈ e.source) :
    e.symm ((0 : ℝ), (0 : K)) = p ∧ ((0 : ℝ), (0 : K)) ∈ e.target := by
  have h : e p = ((0 : ℝ), (0 : K)) := by rw [he, sub_self, hP0, h0]
  exact ⟨by rw [← h]; exact e.left_inv hpe, by rw [← h]; exact e.map_source hpe⟩

/-- W3: small centred boxes lift into any native ball around the centre. -/
theorem exists_box_image_subset_ball {K : Type*} [NormedAddCommGroup K]
    (e : OpenPartialHomeomorph R3 (ℝ × K)) {p : R3} (hp0 : e.symm ((0 : ℝ), (0 : K)) = p)
    (h0t : ((0 : ℝ), (0 : K)) ∈ e.target) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ' : ℝ, ρ' < δ →
      Set.Icc (-ρ') ρ' ×ˢ Metric.closedBall (0 : K) ρ' ⊆ e.target →
      e.symm '' (Set.Icc (-ρ') ρ' ×ˢ Metric.closedBall (0 : K) ρ') ⊆ Metric.ball p r := by
  obtain ⟨δ, hδ, H⟩ := Metric.continuousWithinAt_iff.mp (e.continuousOn_symm _ h0t) r hr
  refine ⟨δ, hδ, fun ρ' hρ' hbt => ?_⟩
  rintro x ⟨⟨s, z⟩, ⟨hs, hz⟩, rfl⟩
  have hd : dist (s, z) ((0 : ℝ), (0 : K)) < δ := by
    rw [Prod.dist_eq]
    have h1 : dist s 0 ≤ ρ' := by
      rw [Real.dist_eq, sub_zero]
      exact abs_le.mpr hs
    have h2 : dist z 0 ≤ ρ' := Metric.mem_closedBall.mp hz
    exact max_lt (by linarith) (by linarith)
  have h := H (hbt ⟨hs, hz⟩) hd
  rw [hp0] at h
  exact h

/-! R8 and WS (REPORT.md v020 §R8/WS, written before this code). -/

/-- R8: `pd` depends only on the germ. -/
theorem pd_congr_of_eventuallyEq {f g : R3 → ℝ} {x : R3} (h : f =ᶠ[nhds x] g) (i : Fin 3) :
    pd i f x = pd i g x := by
  unfold pd
  rw [h.fderiv_eq]

/-- R8: the native `Lop` depends only on the germ. -/
theorem Lop_congr_of_eventuallyEq (a : Fin 3 → Fin 3 → R3 → ℝ) {f g : R3 → ℝ} {x : R3}
    (h : f =ᶠ[nhds x] g) : Lop a f x = Lop a g x := by
  unfold Lop
  refine Finset.sum_congr rfl fun i _ => pd_congr_of_eventuallyEq ?_ i
  filter_upwards [h.eventuallyEq_nhds] with z hz
  simp only [pd_congr_of_eventuallyEq hz]

theorem Lop_zero_fun (a : Fin 3 → Fin 3 → R3 → ℝ) (x : R3) :
    Lop a (fun _ => (0 : ℝ)) x = 0 := by
  simp [Lop, pd]

/-- R8: the residual `Lop b (χ w)` vanishes off the closed transition set. -/
theorem Lop_cutoff_mul_eq_zero (b : Fin 3 → Fin 3 → R3 → ℝ) {chi w : R3 → ℝ}
    {Dset Kset : Set R3} (hts : tsupport chi ⊆ Dset) (hw : ∀ x ∈ Dset, Lop b w x = 0)
    (hdich : ∀ x, x ∉ Kset →
      chi =ᶠ[nhds x] (fun _ => (0 : ℝ)) ∨ chi =ᶠ[nhds x] (fun _ => (1 : ℝ))) :
    ∀ x, x ∉ Kset → Lop b (fun y => chi y * w y) x = 0 := by
  intro x hx
  rcases hdich x hx with h | h
  · have hg : (fun y => chi y * w y) =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
      filter_upwards [h] with y hy
      simp only [hy, zero_mul]
    rw [Lop_congr_of_eventuallyEq b hg]
    exact Lop_zero_fun b x
  · have hx1 : chi x = 1 := h.eq_of_nhds
    have hxD : x ∈ Dset :=
      hts (subset_tsupport chi (Function.mem_support.mpr (by rw [hx1]; exact one_ne_zero)))
    have hg : (fun y => chi y * w y) =ᶠ[nhds x] w := by
      filter_upwards [h] with y hy
      simp only [hy, one_mul]
    rw [Lop_congr_of_eventuallyEq b hg]
    exact hw x hxD

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
