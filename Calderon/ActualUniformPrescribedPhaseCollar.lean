import Calderon.ActualUniformPrescribedPhaseDilationCarleman
import Calderon.ActualCompactParameterCollarResidual
import MixedKernelCenteredRooms
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open Geometry
theorem native_room_collar_sq_uniform_near_dilation (g : MatrixField) (hg : IsAdmissibleMetric g)
    (lamBase : ℝ) {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hdθ : (fun k => pd k θ p) ≠ 0) (hsrc : SrcStrict (fun x => g (lamBase • x)) θ p)
    (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
      (p ∈ e.source ∧ e.symm (0, 0) = p) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ lam0 ρ C τ0 : ℝ, 0 < lam0 ∧ 0 < ρ ∧ 0 < C ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 →
      IsOpen (e.symm '' PhaseCoordinates.roomD l ε R) ∧
      IsOpen (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)) ∧
      e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
        e.symm '' PhaseCoordinates.roomD l ε R ∧
      e.symm '' PhaseCoordinates.closedO l ε R ⊆ e.symm '' PhaseCoordinates.roomD l ε R ∧
      e.symm '' PhaseCoordinates.closedD l ε R ⊆ Metric.ball p r0 ∧
      (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ lambda ∈ closedBall lamBase lam0, ∀ τ : ℝ, τ0 ≤ τ → ∀ w : R3 → ℝ,
        ContDiffOn ℝ ∞ w (e.symm '' PhaseCoordinates.roomD l ε R) →
        (∀ x ∈ e.symm '' PhaseCoordinates.roomD l ε R,
          Lop (fun i k y => EnergyBridge.principalCoefficient g (lambda • y) i k) w x = 0) →
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
  obtain ⟨κ0, hκ0, HK⟩ := exists_kappa_principal_carleman_strictPhase_uniform_near_dilation g hg lamBase hθ p h0 hdθ hsrc
  refine ⟨e, he, hcenter, κ0, hκ0, fun κ hκ hκ' => ?_⟩
  obtain ⟨r, C, τ0, hr, hC, hτ0, hcarl⟩ := HK κ hκ.le hκ'
  obtain ⟨hp0, h0t⟩ := chart_symm_zero e he (map_zero _) h0 hpe
  obtain ⟨δ, hδ, hball⟩ := exists_box_image_subset_ball e hp0 h0t (lt_min hr hr0)
  have hρ' : 0 < min ρ (δ / 2) := lt_min hρ (half_pos hδ)
  refine ⟨r, min ρ (δ / 2), C, τ0, hr, hρ', hC, fun l ε R hε hl hR hlρ hRρ hκh => ?_⟩
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
  let coeff : ℝ→Fin 3→Fin 3→R3→ℝ := fun lambda i k y => principalCoefficient g (lambda • y) i k
  have hbJoint : ∀ i k,JointSmooth fun lambda => coeff lambda i k :=
    fun i k => (contDiff_principalCoefficient_entry g hg i k).comp (contDiff_fst.smul contDiff_snd)
  have hsJoint : ∀ lambda i j x,coeff lambda i j x=coeff lambda j i x := by
    intro lambda i j x
    simpa only [star_trivial] using ((principalCoefficient_posDef g hg (lambda • x)).isHermitian.apply j i)
  have hposJoint : ∀ lambda x,∀ xi:Fin 3→ℝ,xi≠0 → 0 < ∑ i,∑ k,xi i*coeff lambda i k x*xi k := by
    intro lambda x xi hxi
    have h := (principalCoefficient_posDef g hg (lambda • x)).dotProduct_mulVec_pos hxi
    convert h using 1
    simp only [dotProduct,Matrix.mulVec,Fin.sum_univ_three,Pi.star_apply,star_trivial] <;> ring
  obtain ⟨CB,hCB,hBb⟩ := exists_joint_collar_residual_l2_bound coeff hbJoint hsJoint
    (closedBall lamBase r) (isCompact_closedBall _ _) hD hD subset_rfl hcB hBD
    (fun lambda _ x _ xi hxi => hposJoint lambda x xi hxi) hc hcs htsD (beta:=fun _ => (1:ℝ)) continuous_const
  obtain ⟨CH,hCH,hHb⟩ := exists_joint_collar_residual_l2_bound coeff hbJoint hsJoint
    (closedBall lamBase r) (isCompact_closedBall _ _) hD hSo hSD hcH hHSub
    (fun lambda _ x _ xi hxi => hposJoint lambda x xi hxi) hc hcs htsD (beta:=fun _ => (1:ℝ)) continuous_const
  refine ⟨hD, hSo, hSD, hClosedOD, hloc, hDt, CB + CH, add_nonneg hCB hCH,
    fun lambda hlam τ hτ w hw hLw hwint => ?_⟩
  have hb : ∀ i k,ContDiff ℝ ∞ (coeff lambda i k) := fun i k => jointSmooth_slice (hbJoint i k) lambda
  have hu : ContDiff ℝ ∞ (fun y => chi y * w y) :=
    OAI.AnisotropicCalderon.CutoffCommutator.contDiff_mul_of_tsupport_subset hD hc htsD hw
  have hus : HasCompactSupport (fun y => chi y * w y) := hcs.mul_right
  have hutB : tsupport (fun y => chi y * w y) ⊆ Metric.closedBall p r :=
    tsupport_mul_subset_left.trans htsB
  have hcarlu := hcarl lambda hlam τ hτ (fun y => chi y * w y) hu hus hutB
  have hRes := Lop_cutoff_mul_eq_zero (fun i k y => EnergyBridge.principalCoefficient g (lambda • y) i k)
    htsD hLw hdich
  have hLzero : ∀ x, x ∉ e.symm '' PhaseCoordinates.transB l ε R ∪
      e.symm '' (PhaseCoordinates.transT l ε R ∪ PhaseCoordinates.transL l ε R) →
      Lop (fun i k y => EnergyBridge.principalCoefficient g (lambda • y) i k) (fun y => chi y * w y) x = 0 := by
    intro x hx
    refine hRes x fun hK => hx ?_
    obtain ⟨y, hy, rfl⟩ := hK
    rcases hy with (hy | hy) | hy
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨y, Or.inl hy, rfl⟩
    · exact Or.inr ⟨y, Or.inr hy, rfl⟩
  have hLc : Continuous (Lop (fun i k y => EnergyBridge.principalCoefficient g (lambda • y) i k)
      (fun y => chi y * w y)) := by
    unfold Lop
    exact continuous_finsetSum _ fun i _ => (OAI.AnisotropicCalderon.contDiff_pd_apply
      (ContDiff.sum fun k _ => (hb i k).mul
        (OAI.AnisotropicCalderon.contDiff_pd_apply hu))).continuous
  have hL_int : MeasureTheory.Integrable (fun x =>
      Lop (fun i k y => EnergyBridge.principalCoefficient g (lambda • y) i k)
        (fun y => chi y * w y) x ^ 2) :=
    (hLc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.intro (hcB.union hcH)
      (fun x hx => by
        change (Lop (fun i k y => EnergyBridge.principalCoefficient g (lambda • y) i k)
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
            Lop (fun i k y => EnergyBridge.principalCoefficient g (lambda • y) i k)
              (fun y => chi y * w y) x ^ 2) +
        Real.exp (2 * (τ * strictHeight κ (l + 3 * ε))) *
          ∫ x in e.symm '' (PhaseCoordinates.transT l ε R ∪ PhaseCoordinates.transL l ε R),
            Lop (fun i k y => EnergyBridge.principalCoefficient g (lambda • y) i k)
              (fun y => chi y * w y) x ^ 2) :=
    weighted_sq_split (ψ := fun x => θ x - κ * θ x ^ 2) (wO := w) hτ1 hC.le hG hcarlu
      hu_int hL_int hcB.isClosed.measurableSet hcH.isClosed.measurableSet
      hcO.isClosed.measurableSet hLzero (fun x hx => hHB x hx) (fun x hx => hHS x hx)
      (fun x hx => hHO x hx) (fun x hx => by simp only [hone x hx, one_mul])
      (((hw.continuousOn.mono hClosedOD).pow 2).integrableOn_compact hcO)
  have hB1 := hBb lambda hlam w hw hLw hwint
  have hH1 := hHb lambda hlam w hw hLw (hwint.mono_set hSD)
  simp only [one_mul] at hB1 hH1
  have hDn : 0 ≤ ∫ x in e.symm '' PhaseCoordinates.roomD l ε R, w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have hSn : 0 ≤ ∫ x in e.symm '' (PhaseCoordinates.roomStop l ε R ∪
      PhaseCoordinates.roomSlat l ε R), w x ^ 2 :=
    MeasureTheory.integral_nonneg fun x => sq_nonneg (w x)
  have h1 := hB1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCH) hDn)
  have h2 := hH1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCB) hSn)
  exact hW.trans (weighted_two_collar_combine hC.le (Real.exp_pos _).le (Real.exp_pos _).le h1 h2)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
