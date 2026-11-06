import MixedKernelAsymmetricWeights
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

theorem three_level_sq_interpolation_uniform {pB p0 pH C tau0 : ℝ}
    (hB0 : pB < p0) (h0H : p0 < pH) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ A S D : ℝ, 0 ≤ A → 0 ≤ S → A ≤ D →
      (∀ tau : ℝ, tau0 ≤ tau → tau^3 * (Real.exp (2*(tau*p0))*A^2) ≤
        C*(Real.exp (2*(tau*pB))*D^2+Real.exp (2*(tau*pH))*S^2)) →
      A ≤ K*(S^((p0-pB)/(pH-pB))*D^(1-(p0-pB)/(pH-pB))) := by
  refine ⟨2*Real.sqrt C+Real.exp ((p0-pB)*max tau0 1),by positivity,?_⟩
  intro A S D hA hS hAD h
  have ha : 0 < p0-pB := sub_pos.mpr hB0
  have hb : 0 < pH-p0 := sub_pos.mpr h0H
  have hbal := exp_balance (a := p0 - pB) (b := pH - p0)
    (C := Real.sqrt C) (τ0 := max tau0 1) ha hb (Real.sqrt_nonneg _) hA hS hAD
    (by
      intro τ hτ
      have h1 := weighted_sq_to_unsq ((le_max_right tau0 1).trans hτ)
        hC hA (hA.trans hAD) hS (h τ ((le_max_left tau0 1).trans hτ))
      have hE : 0 < Real.exp (τ * p0) := Real.exp_pos _
      have eB : Real.exp (τ * pB) = Real.exp (τ * p0) *
          Real.exp (-((p0 - pB) * τ)) := by
        rw [← Real.exp_add]; congr 1; ring
      have eH : Real.exp (τ * pH) = Real.exp (τ * p0) *
          Real.exp ((pH - p0) * τ) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [eB, eH] at h1
      have h2 : Real.exp (τ * p0) * A ≤ Real.exp (τ * p0) *
          (Real.sqrt C * (Real.exp (-((p0 - pB) * τ)) * D +
            Real.exp ((pH - p0) * τ) * S)) :=
        h1.trans_eq (by ring)
      exact le_of_mul_le_mul_left h2 hE)
  have hsum : p0 - pB + (pH - p0) = pH - pB := by ring
  rw [hsum] at hbal
  have hne : pH - pB ≠ 0 := by
    have hh := add_pos ha hb
    rw [hsum] at hh
    exact hh.ne'
  have hg : (pH - p0) / (pH - pB) = 1 - (p0 - pB) / (pH - pB) := by
    rw [eq_sub_iff_add_eq, ← add_div,
      show pH - p0 + (p0 - pB) = pH - pB by ring, div_self hne]
  rw [hg] at hbal
  exact hbal


theorem native_room_collar_sq_between_dilate (g : MatrixField) (hg : IsAdmissibleMetric g) (lam : ℝ)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => g (lam • x)) θ p) (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    (p ∈ e.source ∧ e.symm (0,0) = p) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ C τ0 : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ l h ε R : ℝ, 0 < ε → 4 * ε < h → h ≤ l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 →
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      PhaseCoordinates.closedD l ε R ⊆ e.target ∧
      IsOpen (e.symm '' PhaseCoordinates.roomD l ε R) ∧
      IsOpen (e.symm '' (PhaseCoordinates.roomStop h ε R ∪ PhaseCoordinates.roomSlat l ε R)) ∧
      e.symm '' (PhaseCoordinates.roomStop h ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
        e.symm '' PhaseCoordinates.roomD l ε R ∧
      e.symm '' PhaseCoordinates.closedO h ε R ⊆ e.symm '' PhaseCoordinates.roomD l ε R ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
        ContDiffOn ℝ ∞ w (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) w x = 0) →
        IntegrableOn (fun x => w x ^ 2) (e.symm '' PhaseCoordinates.roomD l ε R) →
        τ ^ 3 * (Real.exp (2 * (τ * strictHeight κ (-ε))) *
            ∫ x in e.symm '' PhaseCoordinates.closedO h ε R, w x ^ 2) ≤
          C * K * (Real.exp (2 * (τ * strictHeight κ (-l + 3 * ε))) *
              (∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2) +
            Real.exp (2 * (τ * strictHeight κ (h + 3 * ε))) *
              ∫ x in e.symm '' (PhaseCoordinates.roomStop h ε R ∪
                PhaseCoordinates.roomSlat l ε R), w x ^ 2) := by
  have hell : fderiv ℝ θ p ≠ 0 := fun h => hdθ (funext fun k => by simp [pd, h])
  obtain ⟨e, hpe, he, ρ, hρ, hBig, hcut⟩ := PhaseCoordinates.exists_room_cutoff_between hθ p h0 hell
  obtain ⟨κ0, hκ0, HK⟩ := exists_kappa_principal_carleman_strictPhase_dilate g hg lam hθ p h0 hdθ hsrc
  refine ⟨e, he, ⟨hpe,(chart_symm_zero e he (map_zero _) h0 hpe).1⟩, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨-, r, C, τ0, hr, hC, hτ0, hcarl⟩ := HK κ hκ.le hκ'
  obtain ⟨hp0, h0t⟩ := chart_symm_zero e he (map_zero _) h0 hpe
  obtain ⟨δ, hδ, hball⟩ := exists_box_image_subset_ball e hp0 h0t (lt_min hr hr0)
  have hρ' : 0 < min ρ (δ / 2) := lt_min hρ (half_pos hδ)
  refine ⟨min ρ (δ / 2), C, τ0, hρ', hC, fun l h ε R hε hh hhl hR hlρ hRρ hκh => ?_⟩
  have hl : 4 * ε < l := hh.trans_le hhl
  have hρρ : min ρ (δ / 2) ≤ ρ := min_le_left _ _
  have hBig' : Set.Icc (-min ρ (δ / 2)) (min ρ (δ / 2)) ×ˢ
      Metric.closedBall (0 : (fderiv ℝ θ p).ker) (min ρ (δ / 2)) ⊆ e.target :=
    (Set.prod_mono (Set.Icc_subset_Icc (neg_le_neg hρρ) hρρ)
      (Metric.closedBall_subset_closedBall hρρ)).trans hBig
  have hball' := hball (min ρ (δ / 2)) ((min_le_right _ _).trans_lt (half_lt_self hδ)) hBig'
  obtain ⟨chi, hc, hcs, hts, hone, hdich⟩ :=
    hcut l h ε R hε hh hhl hR (hlρ.trans hρρ) (hRρ.trans hρρ)
  have hDbig : (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆
      Set.Icc (-min ρ (δ / 2)) (min ρ (δ / 2)) ×ˢ
        Metric.closedBall (0 : (fderiv ℝ θ p).ker) (min ρ (δ / 2)) :=
    PhaseCoordinates.closedD_subset_big hε hlρ hRρ
  have hDt : (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target :=
    hDbig.trans hBig'
  have hSuD : (PhaseCoordinates.suppBoxBetween l h ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆
      PhaseCoordinates.closedD l ε R :=
    ((PhaseCoordinates.suppBoxBetween_subset_suppBox hhl).trans (PhaseCoordinates.suppBox_subset_roomD hε hl hR)).trans PhaseCoordinates.roomD_subset_closedD
  have htsD : tsupport chi ⊆ e.symm '' PhaseCoordinates.roomD l ε R :=
    hts.trans (Set.image_mono ((PhaseCoordinates.suppBoxBetween_subset_suppBox hhl).trans (PhaseCoordinates.suppBox_subset_roomD hε hl hR)))
  have htsB : tsupport chi ⊆ Metric.closedBall p r :=
    (hts.trans ((Set.image_mono (hSuD.trans hDbig)).trans hball')).trans
      ((Metric.ball_subset_ball (min_le_left r r0)).trans Metric.ball_subset_closedBall)
  have hloc : e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 :=
    ((Set.image_mono hDbig).trans hball').trans (Metric.ball_subset_ball (min_le_right r r0))
  obtain ⟨hD, _, hSo, _, _, hSD, hcB, hBD, hcH, hHSub, hcO, hClosedOD, _, _, _⟩ :=
    native_rooms_between e hε hh hhl hR hDt
  obtain ⟨hHB,hHS,hHO⟩ := native_weight_heights_between e he hκ hε hh hhl hR hκh hDt
  have hb : ∀ i k, ContDiff ℝ ∞ (fun y => EnergyBridge.principalCoefficient g (lam • y) i k) :=
    fun i k => (EnergyBridge.contDiff_principalCoefficient_entry g hg i k).comp
      (contDiff_id.const_smul lam)
  have hs : ∀ i j x, (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) i j x =
      (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) j i x := fun i j x => by
    simpa only [star_trivial] using
      ((EnergyBridge.principalCoefficient_posDef g hg (lam • x)).isHermitian.apply j i)
  have hpos : ∀ x : R3, ∀ ξ : Fin 3 → ℝ, ξ ≠ 0 → 0 < ∑ i, ∑ k,
      ξ i * (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) i k x * ξ k := by
    intro x ξ hξ
    have h := (EnergyBridge.principalCoefficient_posDef g hg (lam • x)).dotProduct_mulVec_pos hξ
    convert h using 1
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Pi.star_apply, star_trivial] <;> ring
  obtain ⟨CB, hCB, hBb⟩ := exists_collar_residual_l2_bound
    (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) hb hs hD hD subset_rfl
    hcB hBD (fun x _ ξ hξ => hpos x ξ hξ) hc hcs htsD (beta := fun _ => (1 : ℝ)) continuous_const
  obtain ⟨CH, hCH, hHb⟩ := exists_collar_residual_l2_bound
    (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) hb hs hD hSo hSD
    hcH hHSub (fun x _ ξ hξ => hpos x ξ hξ) hc hcs htsD (beta := fun _ => (1 : ℝ)) continuous_const
  refine ⟨hloc,hDt,hD, hSo, hSD, hClosedOD, CB + CH, add_nonneg hCB hCH,
    fun τ hτ w hw hLw hwint => ?_⟩
  have hu : ContDiff ℝ ∞ (fun y => chi y * w y) :=
    OAI.AnisotropicCalderon.CutoffCommutator.contDiff_mul_of_tsupport_subset hD hc htsD hw
  have hus : HasCompactSupport (fun y => chi y * w y) := hcs.mul_right
  have hutB : tsupport (fun y => chi y * w y) ⊆ Metric.closedBall p r :=
    tsupport_mul_subset_left.trans htsB
  have hcarlu := hcarl τ hτ (fun y => chi y * w y) hu hus hutB
  have hRes := Lop_cutoff_mul_eq_zero (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
    htsD hLw hdich
  have hLzero : ∀ x, x ∉ e.symm '' PhaseCoordinates.transB l ε R ∪
      e.symm '' (PhaseCoordinates.transT h ε R ∪ PhaseCoordinates.transLBetween l h ε R) →
      Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) (fun y => chi y * w y) x = 0 := by
    intro x hx
    refine hRes x fun hK => hx ?_
    obtain ⟨y, hy, rfl⟩ := hK
    rcases hy with (hy | hy) | hy
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨y, Or.inl hy, rfl⟩
    · exact Or.inr ⟨y, Or.inr hy, rfl⟩
  have hLc : Continuous (Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
      (fun y => chi y * w y)) := by
    unfold Lop
    exact continuous_finsetSum _ fun i _ => (OAI.AnisotropicCalderon.contDiff_pd_apply
      (ContDiff.sum fun k _ => (hb i k).mul
        (OAI.AnisotropicCalderon.contDiff_pd_apply hu))).continuous
  have hL_int : MeasureTheory.Integrable (fun x =>
      Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
        (fun y => chi y * w y) x ^ 2) :=
    (hLc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.intro (hcB.union hcH)
      (fun x hx => by
        change (Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
          (fun y => chi y * w y) x) ^ 2 = 0
        rw [hLzero x hx]
        norm_num))
  have hψc : Continuous (fun x => θ x - κ * θ x ^ 2) :=
    hθ.continuous.sub (continuous_const.mul (hθ.continuous.pow 2))
  have hu_int : MeasureTheory.Integrable (fun x =>
      (Real.exp (τ * (θ x - κ * θ x ^ 2)) * (chi x * w x)) ^ 2) := by
    refine (((Real.continuous_exp.comp (continuous_const.mul hψc)).mul
      hu.continuous).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.intro (show IsCompact (tsupport fun y => chi y * w y) from hus)
          (fun x hx => ?_))
    have hzero : chi x * w x = 0 :=
      (notMem_tsupport_iff_eventuallyEq.mp hx).eq_of_nhds
    change (Real.exp (τ * (θ x - κ * θ x ^ 2)) * (chi x * w x)) ^ 2 = 0
    rw [hzero, mul_zero]
    norm_num
  have hτ1 : 0 ≤ τ := by linarith
  have hG : 0 ≤ ∫ x, ∑ i, pd i (fun y => Real.exp (τ * (θ y - κ * θ y ^ 2)) *
      (chi y * w y)) x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hW : τ ^ 3 * (Real.exp (2 * (τ * strictHeight κ (-ε))) *
        ∫ x in e.symm '' PhaseCoordinates.closedO h ε R, w x ^ 2) ≤
      C * (Real.exp (2 * (τ * strictHeight κ (-l + 3 * ε))) *
          (∫ x in e.symm '' PhaseCoordinates.transB l ε R,
            Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
              (fun y => chi y * w y) x ^ 2) +
        Real.exp (2 * (τ * strictHeight κ (h + 3 * ε))) *
          ∫ x in e.symm '' (PhaseCoordinates.transT h ε R ∪ PhaseCoordinates.transLBetween l h ε R),
            Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
              (fun y => chi y * w y) x ^ 2) :=
    weighted_sq_split (ψ := fun x => θ x - κ * θ x ^ 2) (wO := w) hτ1 hC.le hG hcarlu
      hu_int hL_int hcB.isClosed.measurableSet hcH.isClosed.measurableSet
      hcO.isClosed.measurableSet hLzero (fun x hx => hHB x hx) (fun x hx => hHS x hx)
      (fun x hx => hHO x hx) (fun x hx => by simp only [hone x hx, one_mul])
      (((hw.continuousOn.mono hClosedOD).pow 2).integrableOn_compact hcO)
  have hB1 := hBb w hw hLw hwint
  have hH1 := hHb w hw hLw (hwint.mono_set hSD)
  simp only [one_mul] at hB1 hH1
  have hDn : 0 ≤ ∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hSn : 0 ≤ ∫ x in e.symm '' (PhaseCoordinates.roomStop h ε R ∪
      PhaseCoordinates.roomSlat l ε R), w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have h1 := hB1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCH) hDn)
  have h2 := hH1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCB) hSn)
  exact hW.trans (weighted_two_collar_combine hC.le (Real.exp_pos _).le (Real.exp_pos _).le h1 h2)


theorem native_room_interpolation_between_dilate (g : MatrixField) (hg : IsAdmissibleMetric g) (lam : ℝ)
    {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => g (lam • x)) θ p) (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    (p ∈ e.source ∧ e.symm (0,0) = p) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l h ε R : ℝ, 0 < ε → 4 * ε < h → h ≤ l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 →
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      PhaseCoordinates.closedD l ε R ⊆ e.target ∧
      ∃ Kint : ℝ, 0 < Kint ∧ ∀ w : R3 → ℝ,
        ContDiffOn ℝ ∞ w (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) w x = 0) →
        IntegrableOn (fun x => w x ^ 2) (e.symm '' PhaseCoordinates.roomD l ε R) →
        Real.sqrt (∫ x in e.symm '' PhaseCoordinates.closedO h ε R, w x ^ 2) ≤
          Kint * (Real.sqrt (∫ x in e.symm '' (PhaseCoordinates.roomStop h ε R ∪
                PhaseCoordinates.roomSlat l ε R), w x ^ 2) ^
              ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
                (strictHeight κ (h + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            Real.sqrt (∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2) ^
              (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
                (strictHeight κ (h + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨e, he, hcenter, κ0, hκ0, H⟩ := native_room_collar_sq_between_dilate g hg lam hθ p h0 hdθ hsrc r0 hr0
  refine ⟨e, he, hcenter, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨ρ, C, τ0, hρ, hC, H2⟩ := H κ hκ hκ'
  refine ⟨ρ, hρ, fun l h ε R hε hh hhl hR hlρ hRρ hκh => ?_⟩
  have hl : 4 * ε < l := hh.trans_le hhl
  obtain ⟨hloc,hDt,-, -, -, hOD, K, hK, HW⟩ := H2 l h ε R hε hh hhl hR hlρ hRρ hκh
  have hscale : l+4*ε < 1/(4*κ) := by
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 4*κ)]
    linarith
  have hm := strictPhaseProfile_strictMonoOn hκ
  have hB0 : strictHeight κ (-l+3*ε) < strictHeight κ (-ε) := by
    apply hm
    · exact ⟨by linarith,by linarith⟩
    · exact ⟨by linarith,by linarith⟩
    · linarith
  have h0H : strictHeight κ (-ε) < strictHeight κ (h+3*ε) := by
    apply hm
    · exact ⟨by linarith,by linarith⟩
    · exact ⟨by linarith,by linarith⟩
    · linarith
  obtain ⟨Kint,hKint,HI⟩ := three_level_sq_interpolation_uniform (tau0 := τ0)
    hB0 h0H (mul_nonneg hC.le hK)
  refine ⟨hloc,hDt,Kint, hKint, fun w hw hLw hwint => ?_⟩
  have hOn : 0 ≤ ∫ x in e.symm '' PhaseCoordinates.closedO h ε R, w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hSn : 0 ≤ ∫ x in e.symm '' (PhaseCoordinates.roomStop h ε R ∪
      PhaseCoordinates.roomSlat l ε R), w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hDn : 0 ≤ ∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hOD' : (∫ x in e.symm '' PhaseCoordinates.closedO h ε R, w x ^ 2) ≤
      ∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2 :=
    setIntegral_mono_set hwint
      (Filter.Eventually.of_forall fun x => show (0 : ℝ) ≤ w x ^ 2 from sq_nonneg _)
      hOD.eventuallyLE
  refine HI _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hOD')
    (fun τ hτ => ?_)
  rw [Real.sq_sqrt hOn, Real.sq_sqrt hSn, Real.sq_sqrt hDn]
  exact HW τ hτ w hw hLw hwint

/-- C4h: the same uniform interpolation for the actual `Lp` carriers on the SAME restricted
Lebesgue measures, observed on the OPEN room `e.symm '' roomO`. -/
theorem native_room_interpolation_lp_between_dilate (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam : ℝ) {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => g (lam • x)) θ p) (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    (p ∈ e.source ∧ e.symm (0,0) = p) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l h ε R : ℝ, 0 < ε → 4 * ε < h → h ≤ l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 →
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      PhaseCoordinates.closedD l ε R ⊆ e.target ∧
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) q x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO h ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop h ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO h ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop h ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (h + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (h + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨e, he, hcenter, κ0, hκ0, H⟩ := native_room_interpolation_between_dilate g hg lam hθ p h0 hdθ hsrc r0 hr0
  refine ⟨e, he, hcenter, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨ρ, hρ, H2⟩ := H κ hκ hκ'
  refine ⟨ρ, hρ, fun l h ε R hε hh hhl hR hlρ hRρ hκh => ?_⟩
  have hl : 4 * ε < l := hh.trans_le hhl
  obtain ⟨hloc,hDt,Kint, hKint, HI⟩ := H2 l h ε R hε hh hhl hR hlρ hRρ hκh
  refine ⟨hloc,hDt,Kint, hKint, fun u q hq hqs hLq uO uS hqO hqS => ?_⟩
  obtain ⟨hmem, hnD⟩ := integral_sq_representative_eq_norm_sq u q hq
  obtain ⟨-, hnO⟩ := integral_sq_representative_eq_norm_sq uO q hqO
  obtain ⟨-, hnS⟩ := integral_sq_representative_eq_norm_sq uS q hqS
  have hwint : IntegrableOn (fun x => q x ^ 2) (e.symm '' PhaseCoordinates.roomD l ε R) :=
    hmem.integrable_sq
  have hI := HI q hqs hLq hwint
  rw [hnS, hnD, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hI
  have hOD : e.symm '' PhaseCoordinates.closedO h ε R ⊆
      e.symm '' PhaseCoordinates.roomD l ε R :=
    Set.image_mono ((PhaseCoordinates.closedO_subset_suppBoxBetween hε hl hR).trans
      ((PhaseCoordinates.suppBoxBetween_subset_suppBox hhl).trans (PhaseCoordinates.suppBox_subset_roomD hε hl hR)))
  have hmono : (∫ x in e.symm '' PhaseCoordinates.roomO h ε R, q x ^ 2) ≤
      ∫ x in e.symm '' PhaseCoordinates.closedO h ε R, q x ^ 2 :=
    setIntegral_mono_set (hwint.mono_set hOD)
      (Filter.Eventually.of_forall fun x => show (0 : ℝ) ≤ q x ^ 2 from sq_nonneg _)
      (Set.image_mono PhaseCoordinates.roomO_subset_closedO).eventuallyLE
  calc ‖uO‖ = Real.sqrt (∫ x in e.symm '' PhaseCoordinates.roomO h ε R, q x ^ 2) := by
        rw [hnO, Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (∫ x in e.symm '' PhaseCoordinates.closedO h ε R, q x ^ 2) :=
        Real.sqrt_le_sqrt hmono
    _ ≤ _ := hI

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
