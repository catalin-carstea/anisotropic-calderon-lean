import MixedKernelNativeCrossSeries
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


section CenteredNativeRooms
open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise

theorem native_room_collar_sq_dilate_loc_centered (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam : ℝ) {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => g (lam • x)) θ p)
    (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
      (p ∈ e.source ∧ e.symm (0, 0) = p) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ C τ0 : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 →
      IsOpen (e.symm '' PhaseCoordinates.roomD l ε R) ∧
      IsOpen (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)) ∧
      e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
        e.symm '' PhaseCoordinates.roomD l ε R ∧
      e.symm '' PhaseCoordinates.closedO l ε R ⊆ e.symm '' PhaseCoordinates.roomD l ε R ∧
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
        ContDiffOn ℝ ∞ w (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) w x = 0) →
        IntegrableOn (fun x => w x ^ 2) (e.symm '' PhaseCoordinates.roomD l ε R) →
        τ ^ 3 * (Real.exp (2 * (τ * strictHeight κ (-ε))) *
            ∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2) ≤
          C * K * (Real.exp (2 * (τ * strictHeight κ (-l + 3 * ε))) *
              (∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2) +
            Real.exp (2 * (τ * strictHeight κ (l + 3 * ε))) *
              ∫ x in e.symm '' (PhaseCoordinates.roomStop l ε R ∪
                PhaseCoordinates.roomSlat l ε R), w x ^ 2) := by
  have hell : fderiv ℝ θ p ≠ 0 := fun h => hdθ (funext fun k => by simp [pd, h])
  obtain ⟨e, hpe, he, ρ, hρ, hBig, hcut⟩ := PhaseCoordinates.exists_room_cutoff hθ p h0 hell
  have hcenter : p ∈ e.source ∧ e.symm (0, 0) = p :=
    ⟨hpe, (chart_symm_zero e he (map_zero _) h0 hpe).1⟩
  obtain ⟨κ0, hκ0, HK⟩ := exists_kappa_principal_carleman_strictPhase_dilate g hg lam hθ p h0 hdθ hsrc
  refine ⟨e, he, hcenter, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨-, r, C, τ0, hr, hC, hτ0, hcarl⟩ := HK κ hκ.le hκ'
  obtain ⟨hp0, h0t⟩ := chart_symm_zero e he (map_zero _) h0 hpe
  obtain ⟨δ, hδ, hball⟩ := exists_box_image_subset_ball e hp0 h0t (lt_min hr hr0)
  have hρ' : 0 < min ρ (δ / 2) := lt_min hρ (half_pos hδ)
  refine ⟨min ρ (δ / 2), C, τ0, hρ', hC, fun l ε R hε hl hR hlρ hRρ hκh => ?_⟩
  have hρρ : min ρ (δ / 2) ≤ ρ := min_le_left _ _
  have hBig' : Set.Icc (-min ρ (δ / 2)) (min ρ (δ / 2)) ×ˢ
      Metric.closedBall (0 : (fderiv ℝ θ p).ker) (min ρ (δ / 2)) ⊆ e.target :=
    (Set.prod_mono (Set.Icc_subset_Icc (neg_le_neg hρρ) hρρ)
      (Metric.closedBall_subset_closedBall hρρ)).trans hBig
  have hball' := hball (min ρ (δ / 2)) ((min_le_right _ _).trans_lt (half_lt_self hδ)) hBig'
  obtain ⟨chi, hc, hcs, hts, hone, hdich⟩ :=
    hcut l ε R hε hl hR (hlρ.trans hρρ) (hRρ.trans hρρ)
  have hDbig : (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆
      Set.Icc (-min ρ (δ / 2)) (min ρ (δ / 2)) ×ˢ
        Metric.closedBall (0 : (fderiv ℝ θ p).ker) (min ρ (δ / 2)) :=
    PhaseCoordinates.closedD_subset_big hε hlρ hRρ
  have hDt : (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target :=
    hDbig.trans hBig'
  have hloc : e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 :=
    ((Set.image_mono hDbig).trans hball').trans (Metric.ball_subset_ball (min_le_right _ _))
  have hSuD : (PhaseCoordinates.suppBox l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆
      PhaseCoordinates.closedD l ε R :=
    (PhaseCoordinates.suppBox_subset_roomD hε hl hR).trans PhaseCoordinates.roomD_subset_closedD
  have htsD : tsupport chi ⊆ e.symm '' PhaseCoordinates.roomD l ε R :=
    hts.trans (Set.image_mono (PhaseCoordinates.suppBox_subset_roomD hε hl hR))
  have htsB : tsupport chi ⊆ Metric.closedBall p r :=
    (hts.trans ((Set.image_mono (hSuD.trans hDbig)).trans hball')).trans
      ((Metric.ball_subset_ball (min_le_left _ _)).trans Metric.ball_subset_closedBall)
  obtain ⟨hD, -, hSo, -, -, -, -, -, -, -, hSD', -, -, hcB, hBD, hcH, hHSub, -, -⟩ :=
    PhaseCoordinates.native_rooms e hBig' hε hl hR hlρ hRρ
  have hSD : e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
      e.symm '' PhaseCoordinates.roomD l ε R := subset_closure.trans hSD'
  have hClosedOD : e.symm '' PhaseCoordinates.closedO l ε R ⊆
      e.symm '' PhaseCoordinates.roomD l ε R :=
    Set.image_mono (PhaseCoordinates.closedO_subset_roomD hε hl hR)
  have hOt : (PhaseCoordinates.closedO l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target :=
    ((PhaseCoordinates.closedO_subset_roomD hε hl hR).trans
      PhaseCoordinates.roomD_subset_closedD).trans hDt
  have hcO : IsCompact (e.symm '' PhaseCoordinates.closedO l ε R) :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).image_of_continuousOn
      (e.continuousOn_symm.mono hOt)
  obtain ⟨hHB, hHS, hHO⟩ := native_weight_heights e he hκ hε hl hR hκh hDt
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
  refine ⟨hD, hSo, hSD, hClosedOD, hloc, hDt, CB + CH, add_nonneg hCB hCH,
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
      e.symm '' (PhaseCoordinates.transT l ε R ∪ PhaseCoordinates.transL l ε R) →
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
        ∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2) ≤
      C * (Real.exp (2 * (τ * strictHeight κ (-l + 3 * ε))) *
          (∫ x in e.symm '' PhaseCoordinates.transB l ε R,
            Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k)
              (fun y => chi y * w y) x ^ 2) +
        Real.exp (2 * (τ * strictHeight κ (l + 3 * ε))) *
          ∫ x in e.symm '' (PhaseCoordinates.transT l ε R ∪ PhaseCoordinates.transL l ε R),
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
  have hSn : 0 ≤ ∫ x in e.symm '' (PhaseCoordinates.roomStop l ε R ∪
      PhaseCoordinates.roomSlat l ε R), w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have h1 := hB1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCH) hDn)
  have h2 := hH1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCB) hSn)
  exact hW.trans (weighted_two_collar_combine hC.le (Real.exp_pos _).le (Real.exp_pos _).le h1 h2)

theorem native_room_interpolation_dilate_loc_centered (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam : ℝ) {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => g (lam • x)) θ p)
    (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
      (p ∈ e.source ∧ e.symm (0, 0) = p) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target ∧
      ∃ Kint : ℝ, 0 < Kint ∧ ∀ w : R3 → ℝ,
        ContDiffOn ℝ ∞ w (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          Lop (fun i k y => EnergyBridge.principalCoefficient g (lam • y) i k) w x = 0) →
        IntegrableOn (fun x => w x ^ 2) (e.symm '' PhaseCoordinates.roomD l ε R) →
        Real.sqrt (∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2) ≤
          Kint * (Real.sqrt (∫ x in e.symm '' (PhaseCoordinates.roomStop l ε R ∪
                PhaseCoordinates.roomSlat l ε R), w x ^ 2) ^
              ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
                (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            Real.sqrt (∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2) ^
              (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
                (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨e, he, hcenter, κ0, hκ0, H⟩ := native_room_collar_sq_dilate_loc_centered g hg lam hθ p h0 hdθ hsrc r0 hr0
  refine ⟨e, he, hcenter, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨ρ, C, τ0, hρ, hC, H2⟩ := H κ hκ hκ'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 => ?_⟩
  obtain ⟨-, -, -, hOD, hloc, hDt, K, hK, HW⟩ := H2 l ε R hε hl hR hlρ hRρ hκh
  have hl0 : 0 < l := by linarith
  have hκl : κ * l ≤ 1 / 4 := by
    have := mul_pos hκ hε
    nlinarith
  obtain ⟨Kint, hKint, HI⟩ := strictHeight_interpolation_of_weighted_sq_uniform (τ0 := τ0)
    hκ hl0 hκl hε.le hε4 (mul_nonneg hC.le hK)
  refine ⟨hloc, hDt, Kint, hKint, fun w hw hLw hwint => ?_⟩
  have hOn : 0 ≤ ∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hSn : 0 ≤ ∫ x in e.symm '' (PhaseCoordinates.roomStop l ε R ∪
      PhaseCoordinates.roomSlat l ε R), w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hDn : 0 ≤ ∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hOD' : (∫ x in e.symm '' PhaseCoordinates.closedO l ε R, w x ^ 2) ≤
      ∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2 :=
    setIntegral_mono_set hwint
      (Filter.Eventually.of_forall fun x => show (0 : ℝ) ≤ w x ^ 2 from sq_nonneg _)
      hOD.eventuallyLE
  refine HI _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hOD')
    (fun τ hτ => ?_)
  rw [Real.sq_sqrt hOn, Real.sq_sqrt hSn, Real.sq_sqrt hDn]
  exact HW τ hτ w hw hLw hwint

theorem native_room_interpolation_lp_op_loc_centered (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam : ℝ) {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => g (lam • x)) θ p)
    (r0 : ℝ) (hr0 : 0 < r0) (Q : (R3 → ℝ) → R3 → ℝ)
    (hQ : ∀ u x, Q u x = 0 → Lop (fun i k y => principalCoefficient g (lam • y) i k) u x = 0) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
      (p ∈ e.source ∧ e.symm (0, 0) = p) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target ∧
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R, Q q x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨e, he, hcenter, κ0, hκ0, H⟩ :=
    native_room_interpolation_dilate_loc_centered g hg lam hθ p h0 hdθ hsrc r0 hr0
  refine ⟨e, he, hcenter, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨ρ, hρ, H2⟩ := H κ hκ hκ'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 => ?_⟩
  obtain ⟨hloc, hDt, Kint, hKint, HI⟩ := H2 l ε R hε hl hR hlρ hRρ hκh hε4
  refine ⟨hloc, hDt, Kint, hKint, fun u q hq hqs hQq uO uS hqO hqS => ?_⟩
  obtain ⟨hmem, hnD⟩ := integral_sq_representative_eq_norm_sq u q hq
  obtain ⟨-, hnO⟩ := integral_sq_representative_eq_norm_sq uO q hqO
  obtain ⟨-, hnS⟩ := integral_sq_representative_eq_norm_sq uS q hqS
  have hwint : IntegrableOn (fun x => q x ^ 2) (e.symm '' PhaseCoordinates.roomD l ε R) :=
    hmem.integrable_sq
  have hI := HI q hqs (fun x hx => hQ q x (hQq x hx)) hwint
  rw [hnS, hnD, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hI
  have hOD : e.symm '' PhaseCoordinates.closedO l ε R ⊆
      e.symm '' PhaseCoordinates.roomD l ε R :=
    Set.image_mono (PhaseCoordinates.closedO_subset_roomD hε hl hR)
  have hmono : (∫ x in e.symm '' PhaseCoordinates.roomO l ε R, q x ^ 2) ≤
      ∫ x in e.symm '' PhaseCoordinates.closedO l ε R, q x ^ 2 :=
    setIntegral_mono_set (hwint.mono_set hOD)
      (Filter.Eventually.of_forall fun x => show (0 : ℝ) ≤ q x ^ 2 from sq_nonneg _)
      (Set.image_mono PhaseCoordinates.roomO_subset_closedO).eventuallyLE
  calc ‖uO‖ = Real.sqrt (∫ x in e.symm '' PhaseCoordinates.roomO l ε R, q x ^ 2) := by
        rw [hnO, Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (∫ x in e.symm '' PhaseCoordinates.closedO l ε R, q x ^ 2) :=
        Real.sqrt_le_sqrt hmono
    _ ≤ _ := hI

theorem native_room_interpolation_known_side_op_centered (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lam : ℝ) (p : R3) {ψ : R3 → ℝ} (hψ : ContDiffAt ℝ 2 ψ p) (hψ0 : ψ p = 0)
    (hdψ : (fun k => pd k ψ p) ≠ 0) (r0 : ℝ) (hr0 : 0 < r0) (Q : (R3 → ℝ) → R3 → ℝ)
    (hQ : ∀ u x, Q u x = 0 → Lop (fun i k y => principalCoefficient g (lam • y) i k) u x = 0) :
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧ (∀ k, pd k θ p = pd k ψ p) ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
      (p ∈ e.source ∧ e.symm (0, 0) = p) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      l < c * R ^ 2 / 9 →
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      PhaseCoordinates.closedD l ε R ⊆ e.target ∧
      e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
        {x | 0 < ψ x} ∧
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R, Q q x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  obtain ⟨θ, hθ, h0, hd, hs, c, r, hc, hr, hgap⟩ := exists_srcStrict_phase_known_side
    (fun x => g (lam • x)) p (hg.posDef (lam • p)) hψ hψ0 hdψ
  have hdθ : (fun k => pd k θ p) ≠ 0 := by
    have h' : (fun k => pd k θ p) = fun k => pd k ψ p := funext hd
    rw [h']
    exact hdψ
  obtain ⟨e, he, hcenter, κ0, hκ0, H⟩ := native_room_interpolation_lp_op_loc_centered g hg lam hθ p h0 hdθ hs
    (min r0 r) (lt_min hr0 hr) Q hQ
  refine ⟨θ, hθ, h0, hd, c, hc, e, he, hcenter, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨ρ, hρ, H2⟩ := H κ hκ hκ'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 hlR => ?_⟩
  obtain ⟨hloc, hDt, Kint, hKint, HI⟩ := H2 l ε R hε hl hR hlρ hRρ hκh hε4
  refine ⟨hloc.trans (Metric.ball_subset_ball (min_le_left _ _)), hDt, ?_, Kint, hKint, HI⟩
  rintro x ⟨u, hu, rfl⟩
  have huD : u ∈ PhaseCoordinates.closedD l ε R := by
    rcases hu with hu | hu
    · exact PhaseCoordinates.roomD_subset_closedD (PhaseCoordinates.closedStop_subset_roomD
        hε hl hR (PhaseCoordinates.roomStop_subset_closedStop hu))
    · exact PhaseCoordinates.roomD_subset_closedD (PhaseCoordinates.closedSlat_subset_roomD
        hε hl hR (PhaseCoordinates.roomSlat_subset_closedSlat hu))
  have hxb : e.symm u ∈ Metric.ball p r :=
    Metric.ball_subset_ball (min_le_right _ _) (hloc ⟨u, huD, rfl⟩)
  have hu1 : e (e.symm u) = u := e.right_inv (hDt huD)
  rw [he] at hu1
  have hθu : θ (e.symm u) = u.1 := congrArg Prod.fst hu1
  have hPu : (fderiv ℝ θ p).ker.orthogonalProjectionOnto (e.symm u - p) = u.2 :=
    congrArg Prod.snd hu1
  have hnorm : ‖u.2‖ ≤ ‖e.symm u - p‖ := by
    rw [← hPu]
    exact Submodule.norm_orthogonalProjectionOnto_apply_le _ _
  have hn0 : 0 ≤ c * ‖e.symm u - p‖ ^ 2 := mul_nonneg hc.le (sq_nonneg _)
  refine hgap _ hxb ?_
  rw [hθu]
  rcases hu with hu | hu
  · have h' : u ∈ Set.Ioo (l + ε / 2) (l + 7 * ε / 2) ×ˢ
        Metric.ball (0 : (fderiv ℝ θ p).ker) (7 * R / 8) := hu
    have := h'.1.1
    have : 0 < l := by linarith
    linarith
  · have h' : u ∈ Set.Ioo (-l + ε) (l + 7 * ε / 2) ×ˢ
        {z : (fderiv ℝ θ p).ker | R / 3 < ‖z‖ ∧ ‖z‖ < 7 * R / 8} := hu
    have h1 := h'.1.1
    have h2 : R / 3 < ‖e.symm u - p‖ := h'.2.1.trans_le hnorm
    have h3 : R ^ 2 / 9 < ‖e.symm u - p‖ ^ 2 := by nlinarith
    have h4 : c * (R ^ 2 / 9) < c * ‖e.symm u - p‖ ^ 2 := mul_lt_mul_of_pos_left h3 hc
    have h5 : c * (R ^ 2 / 9) = c * R ^ 2 / 9 := by ring
    linarith

theorem native_known_side_rooms_loc_centered (S : KnownSideSourceData) (g : MatrixField)
    (hg : IsAdmissibleMetric g) (lam : ℝ) (hlam : 0 < lam) (a : ℝ)
    (hball : Metric.ball (0 : R3) a ⊆ S.coordinateRoom)
    (hW : {z ∈ Metric.ball (0 : R3) a | S.separating_function z < 0} ⊆ S.W)
    (p : R3) (hp : lam • p ∈ Metric.ball (0 : R3) a) (hp0 : S.separating_function (lam • p) = 0)
    (hdp : fderiv ℝ S.separating_function (lam • p) ≠ 0) (r0 : ℝ) (hr0 : 0 < r0)
    (Q : (R3 → ℝ) → R3 → ℝ)
    (hQ : ∀ u x, Q u x = 0 → Lop (fun i k y => principalCoefficient g (lam • y) i k) u x = 0) :
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧
      (∀ k, pd k θ p = pd k (fun x => -S.separating_function (lam • x)) p) ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
      (p ∈ e.source ∧ e.symm (0, 0) = p) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      l < c * R ^ 2 / 9 →
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      PhaseCoordinates.closedD l ε R ⊆ e.target ∧
      (∀ x ∈ e.symm '' PhaseCoordinates.closedD l ε R, lam • x ∈ S.coordinateRoom) ∧
      (∀ x ∈ e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R),
        lam • x ∈ S.W) ∧
      ∃ Kint : ℝ, 0 < Kint ∧
        ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
          (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
          (u : R3 → ℝ) →
        ContDiffOn ℝ ∞ q (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R, Q q x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
          (uS : Lp ℝ 2 ((volume : Measure R3).restrict
            (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
        q =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
          (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
          (uS : R3 → ℝ) →
        ‖uO‖ ≤ Kint * (‖uS‖ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) *
            ‖u‖ ^ (1 - (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
              (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)))) := by
  have hcd : ContDiffAt ℝ ∞ S.separating_function (lam • p) :=
    S.separating_function_smooth.contDiffAt (S.coordinateRoom_open.mem_nhds (hball hp))
  have hψ : ContDiffAt ℝ 2 (fun x : R3 => -S.separating_function (lam • x)) p :=
    ((hcd.comp p (contDiffAt_id.const_smul lam)).neg).of_le (by simp)
  have hψ0 : (fun x : R3 => -S.separating_function (lam • x)) p = 0 := by
    simp [hp0]
  have hF : HasFDerivAt (fun x : R3 => -S.separating_function (lam • x))
      (-((fderiv ℝ S.separating_function (lam • p)).comp
        (lam • ContinuousLinearMap.id ℝ R3))) p :=
    ((hcd.differentiableAt (by simp)).hasFDerivAt.comp p
      ((hasFDerivAt_id p).const_smul lam)).neg
  have hdk : ∀ k, pd k (fun x : R3 => -S.separating_function (lam • x)) p =
      -(lam * fderiv ℝ S.separating_function (lam • p) (EuclideanSpace.single k 1)) := by
    intro k
    unfold pd
    rw [hF.fderiv]
    simp
  have hdψ : (fun k => pd k (fun x : R3 => -S.separating_function (lam • x)) p) ≠ 0 := by
    intro h
    apply hdp
    ext h'
    rw [clm_apply_eq_sum_pd]
    simp only [ContinuousLinearMap.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk := congrFun h k
    simp only [Pi.zero_apply] at hk
    rw [hdk k] at hk
    have : fderiv ℝ S.separating_function (lam • p) (EuclideanSpace.single k 1) = 0 := by
      have h2 : lam * fderiv ℝ S.separating_function (lam • p) (EuclideanSpace.single k 1) = 0 := by
        linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 hlam.ne'
      · exact h3
    rw [this, zero_mul]
  have hr1 : 0 < (a - ‖lam • p‖) / lam := by
    have : ‖lam • p‖ < a := by simpa using hp
    exact div_pos (by linarith) hlam
  obtain ⟨θ, hθ, h0, hd, c, hc, e, he, hcenter, κ0, hκ0, H⟩ := native_room_interpolation_known_side_op_centered
    g hg lam p hψ hψ0 hdψ (min r0 ((a - ‖lam • p‖) / lam)) (lt_min hr0 hr1) Q hQ
  refine ⟨θ, hθ, h0, hd, c, hc, e, he, hcenter, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨ρ, hρ, H2⟩ := H κ hκ hκ'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 hlR => ?_⟩
  obtain ⟨hloc, hDt, hknown, Kint, hKint, HI⟩ := H2 l ε R hε hl hR hlρ hRρ hκh hε4 hlR
  have hsmall : ∀ x ∈ e.symm '' PhaseCoordinates.closedD l ε R,
      lam • x ∈ Metric.ball (0 : R3) a := by
    intro x hx
    have h1 : ‖x - p‖ < (a - ‖lam • p‖) / lam := by
      have := hloc hx
      rw [Metric.mem_ball, dist_eq_norm] at this
      exact this.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ hlam] at h1
    have h2 : ‖lam • x - lam • p‖ = ‖x - p‖ * lam := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hlam, mul_comm]
    have h3 := norm_sub_norm_le (lam • x) (lam • p)
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hSD : e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
      e.symm '' PhaseCoordinates.closedD l ε R := by
    refine Set.image_mono fun u hu => ?_
    rcases hu with hu | hu
    · exact PhaseCoordinates.roomD_subset_closedD (PhaseCoordinates.closedStop_subset_roomD
        hε hl hR (PhaseCoordinates.roomStop_subset_closedStop hu))
    · exact PhaseCoordinates.roomD_subset_closedD (PhaseCoordinates.closedSlat_subset_roomD
        hε hl hR (PhaseCoordinates.roomSlat_subset_closedSlat hu))
  refine ⟨hloc.trans (Metric.ball_subset_ball (min_le_left _ _)), hDt,
    fun x hx => hball (hsmall x hx), fun x hx => hW ⟨hsmall x (hSD hx), ?_⟩, Kint, hKint, HI⟩
  have := hknown hx
  simp only [Set.mem_setOf_eq] at this
  linarith

theorem native_first_basis_arm_loc_centered (S : KnownSideSourceData) :
    ∃ a1 : ℝ, 0 < a1 ∧ ∀ lam : ℝ, 0 < lam → ∀ r0 : ℝ, 0 < r0 → ∀ p : R3,
    lam • p ∈ Metric.ball (0 : R3) a1 → S.separating_function (lam • p) = 0 →
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧
      (∀ k, pd k θ p = pd k (fun x => -S.separating_function (lam • x)) p) ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
      (p ∈ e.source ∧ e.symm (0, 0) = p) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      l < c * R ^ 2 / 9 →
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      PhaseCoordinates.closedD l ε R ⊆ e.target ∧
      IsOpen (e.symm '' PhaseCoordinates.roomD l ε R) ∧
      e.symm '' PhaseCoordinates.roomO l ε R ⊆ e.symm '' PhaseCoordinates.roomD l ε R ∧
      e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
        e.symm '' PhaseCoordinates.roomD l ε R ∧
      (∀ x ∈ e.symm '' PhaseCoordinates.closedD l ε R, lam • x ∈ S.coordinateRoom) ∧
      (∀ x ∈ e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R),
        lam • x ∈ S.W) ∧
      1 / 2 < (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
        (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)) ∧
      (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
        (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)) < 1 ∧
      ∃ Kint : ℝ, 0 < Kint ∧
      FirstBasisArmOn S lam (e.symm '' PhaseCoordinates.roomD l ε R)
        (e.symm '' PhaseCoordinates.roomO l ε R)
        (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)) Kint
        ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
          (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) := by
  obtain ⟨a1, ha1, hball, hW, hnc⟩ := separating_noncritical_ball S
  refine ⟨a1, ha1, fun lam hlam r0 hr0 p hp hp0 => ?_⟩
  obtain ⟨θ, hθ, h0, hd, c, hc, e, he, hcenter, κ0, hκ0, H1⟩ := native_known_side_rooms_loc_centered S S.g1
    S.g1_admissible lam hlam a1 hball hW p hp hp0 (hnc _ hp) r0 hr0
    (fun u x => coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) u) x)
    (fun u x h => (coordinateFluxDivergence_metricDivergenceFlux_eq_Lop _ u x).symm.trans h)
  refine ⟨θ, hθ, h0, hd, c, hc, e, he, hcenter, κ0, hκ0, fun κ hκ hκ0' => ?_⟩
  obtain ⟨ρ, hρ, H2⟩ := H1 κ hκ hκ0'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 hlR => ?_⟩
  obtain ⟨hloc, hDt, hroom, hW', Kint, hKint, HI⟩ := H2 l ε R hε hl hR hlρ hRρ hκh hε4 hlR
  obtain ⟨hDo, hOD, hSD⟩ := native_room_open_subsets e hε hl hR hDt
  have hκl : κ * l ≤ 1 / 4 := by nlinarith [mul_pos hκ hε]
  obtain ⟨-, -, hg1, hg2⟩ := strictExponent_bounds hκ (by linarith) hκl hε.le hε4
  exact ⟨hloc, hDt, hDo, hOD, hSD, hroom, hW', hg1, hg2, Kint, hKint,
    first_basis_arm_on_of_room S lam _ _ _ HI⟩

theorem native_second_coefficient_arm_loc_centered (S : KnownSideSourceData) (L : ℝ) :
    ∃ a1 : ℝ, 0 < a1 ∧ ∀ lam : ℝ, 0 < lam → ∀ r0 : ℝ, 0 < r0 → ∀ p : R3,
    lam • p ∈ Metric.ball (0 : R3) a1 → S.separating_function (lam • p) = 0 →
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧
      (∀ k, pd k θ p = pd k (fun x => -S.separating_function (lam • x)) p) ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
      (p ∈ e.source ∧ e.symm (0, 0) = p) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      l < c * R ^ 2 / 9 →
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      PhaseCoordinates.closedD l ε R ⊆ e.target ∧
      IsOpen (e.symm '' PhaseCoordinates.roomD l ε R) ∧
      e.symm '' PhaseCoordinates.roomO l ε R ⊆ e.symm '' PhaseCoordinates.roomD l ε R ∧
      e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
        e.symm '' PhaseCoordinates.roomD l ε R ∧
      (∀ x ∈ e.symm '' PhaseCoordinates.closedD l ε R, lam • x ∈ S.coordinateRoom) ∧
      (∀ x ∈ e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R),
        lam • x ∈ S.W) ∧
      1 / 2 < (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
        (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)) ∧
      (strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
        (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)) < 1 ∧
      ∃ Kint : ℝ, 0 < Kint ∧
      ∀ (b : R3 → ℝ), ContDiffOn ℝ ∞ b (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          normalizedSecondLaplacian S.g1 S.g2 L lam b x = 0) →
      ∀ (bD : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)))
        (bO : Lp ℝ 2 ((volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)))
        (bS : Lp ℝ 2 ((volume : Measure R3).restrict
          (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)))),
      b =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomD l ε R)]
        (bD : R3 → ℝ) →
      b =ᵐ[(volume : Measure R3).restrict (e.symm '' PhaseCoordinates.roomO l ε R)]
        (bO : R3 → ℝ) →
      b =ᵐ[(volume : Measure R3).restrict
        (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R))]
        (bS : R3 → ℝ) →
      ∀ M μ : ℝ, 0 < μ → 0 ≤ M → ‖bS‖ ≤ M → ‖bD‖ ≤ M / μ →
        ‖bO‖ ≤ Kint * M * μ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
            (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)) - 1) ∧
        μ * ‖bO‖ ≤ Kint * M * μ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
            (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε))) := by
  obtain ⟨a1, ha1, hball, hW, hnc⟩ := separating_noncritical_ball S
  refine ⟨a1, ha1, fun lam hlam r0 hr0 p hp hp0 => ?_⟩
  obtain ⟨θ, hθ, h0, hd, c, hc, e, he, hcenter, κ0, hκ0, H1⟩ := native_known_side_rooms_loc_centered S S.g2
    S.g2_admissible lam hlam a1 hball hW p hp hp0 (hnc _ hp) r0 hr0
    (fun u x => normalizedSecondLaplacian S.g1 S.g2 L lam u x)
    (fun u x h => (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2 S.g1_admissible
      S.g2_admissible L lam u x).mp h)
  refine ⟨θ, hθ, h0, hd, c, hc, e, he, hcenter, κ0, hκ0, fun κ hκ hκ0' => ?_⟩
  obtain ⟨ρ, hρ, H2⟩ := H1 κ hκ hκ0'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 hlR => ?_⟩
  obtain ⟨hloc, hDt, hroom, hW', Kint, hKint, HI⟩ := H2 l ε R hε hl hR hlρ hRρ hκh hε4 hlR
  obtain ⟨hDo, hOD, hSD⟩ := native_room_open_subsets e hε hl hR hDt
  have hκl : κ * l ≤ 1 / 4 := by nlinarith [mul_pos hκ hε]
  obtain ⟨-, -, hg1, hg2⟩ := strictExponent_bounds hκ (by linarith) hκl hε.le hε4
  refine ⟨hloc, hDt, hDo, hOD, hSD, hroom, hW', hg1, hg2, Kint, hKint,
    fun b hb hP bD bO bS hbD hbO hbS M μ hμ hM hSb hDb => ?_⟩
  have h := HI bD b hbD hb hP bO bS hbO hbS
  have h1 := interp_coeff_bound hμ hM hKint.le (norm_nonneg _) hSb (norm_nonneg _) hDb
    (by linarith) hg2.le h
  refine ⟨h1, ?_⟩
  calc μ * ‖bO‖ ≤ μ * (Kint * M * μ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
          (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)) - 1)) :=
        mul_le_mul_of_nonneg_left h1 hμ.le
    _ = Kint * M * (μ * μ ^ ((strictHeight κ (-ε) - strictHeight κ (-l + 3 * ε)) /
          (strictHeight κ (l + 3 * ε) - strictHeight κ (-l + 3 * ε)) - 1)) := by ring
    _ = _ := by rw [mul_rpow_sub_one hμ]

/-- The actual center is in the actual open inner room. -/
theorem chart_room_contains_center {θ : R3 → ℝ} {p : R3}
    (e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker))
    (hcenter : e.symm (0, 0) = p) {l ε R : ℝ}
    (hε : 0 < ε) (hl : 4 * ε < l) (hR : 0 < R) :
    p ∈ e.symm '' PhaseCoordinates.roomO l ε R := by
  have hz : ((0, 0) : ℝ × (fderiv ℝ θ p).ker) ∈ PhaseCoordinates.roomO l ε R :=
    Set.mk_mem_prod ⟨by linarith, by linarith⟩ (Metric.mem_ball_self (half_pos hR))
  exact ⟨(0, 0), hz, hcenter⟩

/-- Data-preserving strengthening, with the exact compact buffers on the same pair. -/
def CenteredCommonPairFacts (S : KnownSideSourceData) (lam r0 : ℝ) (p1 p2 : R3)
    (D1 O1 T D2 O2 S2 : Set R3) (K1i K2i γ1 γ2 : ℝ) : Prop :=
  CommonPairFacts S lam r0 p1 p2 D1 O1 T D2 O2 S2 K1i K2i γ1 γ2 ∧
  p1 ∈ O1 ∧ p2 ∈ O2 ∧ IsConnected D2 ∧ S2.Nonempty ∧
  ∃ K1 KT J2 JS : Set R3, IsCompact K1 ∧ IsCompact KT ∧ IsCompact J2 ∧ IsCompact JS ∧
    D1 ⊆ K1 ∧ T ⊆ KT ∧ KT ⊆ D1 ∧ D2 ⊆ J2 ∧ S2 ⊆ JS ∧ JS ⊆ D2 ∧
    KT ×ˢ J2 ⊆ initialCross S lam ∧ K1 ×ˢ JS ⊆ initialCross S lam

theorem native_common_pair_centered (S : KnownSideSourceData) (L : ℝ) :
    ∃ a1 : ℝ, 0 < a1 ∧ ∀ lam : ℝ, 0 < lam → ∀ r0 : ℝ, 0 < r0 → ∀ p1 p2 : R3,
    lam • p1 ∈ Metric.ball (0 : R3) a1 → S.separating_function (lam • p1) = 0 →
    lam • p2 ∈ Metric.ball (0 : R3) a1 → S.separating_function (lam • p2) = 0 →
    r0 + r0 ≤ dist p1 p2 →
    ∃ (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1D1 : O1 ⊆ D1) (T : Set R3)
      (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3) (K1i K2i γ1 γ2 : ℝ),
      CenteredCommonPairFacts S lam r0 p1 p2 D1 O1 T D2 O2 S2 K1i K2i γ1 γ2 ∧
      SecondCoefficientInterpolationOn S L lam D2 O2 S2 K2i γ2 ∧
      FirstBasisArmOn S lam D1 O1 T K1i γ1 ∧
      ∃ (ι : Type) (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ),
        CrossSeriesOn S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ := by
  obtain ⟨a1, ha1, H1⟩ := native_first_basis_arm_loc_centered S
  obtain ⟨a2, ha2, H2⟩ := native_second_coefficient_arm_loc_centered S L
  refine ⟨min a1 a2, lt_min ha1 ha2,
    fun lam hlam r0 hr0 p1 p2 hp1 hp10 hp2 hp20 hsep => ?_⟩
  obtain ⟨θ1, -, -, -, c1, hc1, e1, -, hcenter1, κ1, hκ1, F1⟩ := H1 lam hlam r0 hr0 p1
    (Metric.ball_subset_ball (min_le_left _ _) hp1) hp10
  obtain ⟨θ2, -, -, -, c2, hc2, e2, -, hcenter2, κ2, hκ2, F2⟩ := H2 lam hlam r0 hr0 p2
    (Metric.ball_subset_ball (min_le_right _ _) hp2) hp20
  have hκ : 0 < min κ1 κ2 := lt_min hκ1 hκ2
  obtain ⟨ρ1, hρ1, G1⟩ := F1 (min κ1 κ2) hκ (min_le_left _ _)
  obtain ⟨ρ2, hρ2, G2⟩ := F2 (min κ1 κ2) hκ (min_le_right _ _)
  obtain ⟨l, ε, R, hε, hl5, hR, hlρ, hRρ, hκl, hεκ, hlR⟩ :=
    exists_slack_params hκ (lt_min hρ1 hρ2) (lt_min hc1 hc2)
  obtain ⟨⟨hl, hlρ1, hRρ1, hκ1', hε1, hlR1⟩, hs1, hs1', hs1''⟩ := slack_params_mono hκ
    (min_le_left ρ1 ρ2) (min_le_left c1 c2) hε hl5 hR hlρ hRρ hκl hεκ hlR
  obtain ⟨⟨-, hlρ2, hRρ2, hκ2', hε2, hlR2⟩, hs2, hs2', hs2''⟩ := slack_params_mono hκ
    (min_le_right ρ1 ρ2) (min_le_right c1 c2) hε hl5 hR hlρ hRρ hκl hεκ hlR
  obtain ⟨hloc1, hDt1, hDo1, hOD1, hSD1, hroom1, -, hg11, hg12, K1i, hK1i, HA⟩ :=
    G1 l ε R hε hl hR hlρ1 hRρ1 hκ1' hε1 hlR1
  obtain ⟨hloc2, hDt2, hDo2, hOD2, hSD2, hroom2, -, hg21, hg22, K2i, hK2i, HB2⟩ :=
    G2 l ε R hε hl hR hlρ2 hRρ2 hκ2' hε2 hlR2
  have hKTW := closedCollar_mem_of_open_collars (⇑e1.symm) (fun x => lam • x ∈ S.W) hκ
    (fun l' ε' R' a b c d e f g h => (G1 l' ε' R' a b c d e f g h).2.2.2.2.2.2.1)
    hε hl5 hR hs1 hs1' (by linarith) (by linarith) hs1''
  have hJSW := closedCollar_mem_of_open_collars (⇑e2.symm) (fun x => lam • x ∈ S.W) hκ
    (fun l' ε' R' a b c d e f g h => (G2 l' ε' R' a b c d e f g h).2.2.2.2.2.2.1)
    hε hl5 hR hs2 hs2' (by linarith) (by linarith) hs2''
  obtain ⟨hK1, hKT, hKTK1, hTKT, hD1K1⟩ := closedRooms_isCompact e1 hε hl hR hDt1
  obtain ⟨hJ2, hJS, hJSJ2, hS2JS, hD2J2⟩ := closedRooms_isCompact e2 hε hl hR hDt2
  obtain ⟨hconn, hO1o, hTo, hTne, hKTD1⟩ := chart_room_facts e1 hε hl hR hDt1
  obtain ⟨hconn2, hO2o, hS2o, hS2ne, hJSD2⟩ := chart_room_facts e2 hε hl hR hDt2
  have hp1O := chart_room_contains_center e1 hcenter1.2 hε hl hR
  have hp2O := chart_room_contains_center e2 hcenter2.2 hε hl hR
  have hdisj : Disjoint (e1.symm '' PhaseCoordinates.closedD l ε R)
      (e2.symm '' PhaseCoordinates.closedD l ε R) :=
    Disjoint.mono hloc1 hloc2 (Metric.ball_disjoint_ball hsep)
  obtain ⟨hrow, hobs⟩ := pair_cross_subset S lam hroom1 hroom2 hKTK1 hJSJ2 hKTW hJSW hdisj
  have HB : SecondCoefficientInterpolationOn S L lam (e2.symm '' PhaseCoordinates.roomD l ε R)
      (e2.symm '' PhaseCoordinates.roomO l ε R)
      (e2.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)) K2i
      ((strictHeight (min κ1 κ2) (-ε) - strictHeight (min κ1 κ2) (-l + 3 * ε)) /
        (strictHeight (min κ1 κ2) (l + 3 * ε) - strictHeight (min κ1 κ2) (-l + 3 * ε))) :=
    fun b hb hP bD bO bS h1 h2 h3 M μ hμ hM hS hD =>
      (HB2 b hb hP bD bO bS h1 h2 h3 M μ hμ hM hS hD).1
  obtain ⟨ι, w, μ, hser⟩ := cross_series_of_rooms S L lam hlam _ _ _ _ _ _ _ _ _ _ hDo1 hconn
    hOD1 hTo hTne hKT hTKT hKTD1 hSD1 hK1 hD1K1 hDo2 hOD2 hS2o hJ2 hD2J2 hJS hS2JS hrow hobs
    hK1i hg11 hg21 HA HB
  refine ⟨_, hDo1, _, hOD1, _, hSD1, _, _, _, K1i, K2i, _, _,
    ⟨⟨fun x hx => hloc1 (hD1K1 hx), fun y hy => hloc2 (hD2J2 hy),
      hdisj.mono hD1K1 hD2J2, hDo1, hconn, hO1o, hOD1, hTo, hTne, hSD1, hDo2, hO2o, hOD2, hS2o,
      hSD2, fun x hx => hroom1 x (hD1K1 hx), fun y hy => hroom2 y (hD2J2 hy),
      fun x hx => hKTW x (hTKT hx), fun y hy => hJSW y (hS2JS hy),
      hK1i, hK2i, hg11, hg12, hg21, hg22⟩, hp1O, hp2O, hconn2, hS2ne,
      _, _, _, _, hK1, hKT, hJ2, hJS, hD1K1, hTKT, hKTD1, hD2J2, hS2JS, hJSD2, hrow, hobs⟩,
    HB, HA, ι, w, μ, hser⟩

end CenteredNativeRooms

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
