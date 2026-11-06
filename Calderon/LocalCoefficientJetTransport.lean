import Calderon.LocalParameterJetTransport
import Calderon.ActualFramedMixedRadialJets
import Calderon.PositiveMatrixPointCalculus

/-! Raw determinant coefficients are smooth only at positive points of the geometric room. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MetricOperator
open ConnectionError NormalCoordinatesFrame
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem contDiffAt_matrixVolumeDensity_of_posDef
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (G : E → Matrix (Fin 3) (Fin 3) ℝ) (x : E)
    (hG : ContDiffAt ℝ ∞ G x) (hpos : (G x).PosDef) :
    ContDiffAt ℝ ∞ (matrixVolumeDensity G) x := by
  exact (contDiffAt_positiveMatrix_volumeDensity (G x) hpos).comp x hG

theorem contDiffAt_matrixPrincipalCoefficient_of_posDef
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (G : E → Matrix (Fin 3) (Fin 3) ℝ) (x : E)
    (hG : ContDiffAt ℝ ∞ G x) (hpos : (G x).PosDef) :
    ContDiffAt ℝ ∞ (matrixPrincipalCoefficient G) x := by
  exact (contDiffAt_positiveMatrix_principalCoefficient (G x) hpos).comp x hG

theorem centerSpatialRadius_eventuallyEq_on_geometric_room
    (F G : (R3 × ℝ) × R3 → V) (ε : ℝ) (hε : 0 < ε) (y0 : R3)
    (heq : ∀ p : (R3 × ℝ) × R3, dist p.1 (y0,0) ≤ ε/4 → ‖p.2‖ ≤ 1 → F p = G p)
    (y z : R3) (r : ℝ) (hy : ‖y-y0‖ < ε/8) (hz : ‖z‖ < 1)
    (hr : |r| ≤ ε/16) :
    centerSpatialRadius F =ᶠ[𝓝 ((y,z),r)] centerSpatialRadius G := by
  let U : Set ((R3 × R3) × ℝ) :=
    {p | dist (p.1.1,p.2) (y0,0) < ε/4 ∧ ‖p.1.2‖ < 1}
  have hd : Continuous (fun p : (R3 × R3) × ℝ => dist (p.1.1,p.2) (y0,0)) :=
    (continuous_fst.fst.prodMk continuous_snd).dist continuous_const
  have hn : Continuous (fun p : (R3 × R3) × ℝ => ‖p.1.2‖) :=
    continuous_fst.snd.norm
  have hU : IsOpen U := (isOpen_lt hd continuous_const).inter (isOpen_lt hn continuous_const)
  have hp : ((y,z),r) ∈ U := by
    refine ⟨?_,hz⟩
    rw [dist_eq_norm]
    change max ‖y-y0‖ ‖r-(0 : ℝ)‖ < ε/4
    rw [sub_zero,Real.norm_eq_abs]
    exact max_lt (by linarith) (by linarith)
  filter_upwards [hU.mem_nhds hp] with p hp
  exact heq ((p.1.1,p.2),p.1.2) hp.1.le hp.2.le

theorem coefficientMixedJet_eq_of_local_raw_smoothness
    (F G : (R3 × ℝ) × R3 → V) (hF : ContDiff ℝ ∞ F)
    (ε : ℝ) (hε : 0 < ε) (y0 : R3)
    (hG : ∀ p : (R3 × ℝ) × R3, dist p.1 (y0,0) ≤ ε/4 → ‖p.2‖ ≤ 1 →
      ContDiffAt ℝ ∞ G p)
    (heq : ∀ p : (R3 × ℝ) × R3, dist p.1 (y0,0) ≤ ε/4 → ‖p.2‖ ≤ 1 → F p = G p)
    (j : ℕ) (y z : R3) (r : ℝ) (hy : ‖y-y0‖ ≤ ε/16) (hz : ‖z‖ ≤ 1)
    (hr : |r| ≤ ε/16) :
    coefficientMixedJet j F ((y,z),r) = coefficientMixedJet j G ((y,z),r) := by
  let s : Set (R3 × R3) := ball y0 (ε/8) ×ˢ ball (0 : R3) 1
  let t : Set (R3 × R3) := closedBall y0 (ε/8) ×ˢ closedBall (0 : R3) 1
  have hcl : closure s = t := by
    simp only [s,t,closure_prod_eq,closure_ball y0 (by positivity : ε/8 ≠ 0),
      closure_ball (0 : R3) (by norm_num : (1 : ℝ) ≠ 0)]
  have hst : s ⊆ t := by
    intro p hp
    exact ⟨ball_subset_closedBall hp.1,ball_subset_closedBall hp.2⟩
  have hts : t ⊆ closure s := by rw [hcl]
  have hc : ContDiff ℝ ∞ (fun p : (R3 × R3) × ℝ => ((p.1.1,p.2),p.1.2)) :=
    (contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd
  have hlocalG : ∀ p ∈ t, ContDiffAt ℝ ∞ (centerSpatialRadius G) (p,r) := by
    intro p hp
    have hy' : ‖p.1-y0‖ ≤ ε/8 := by
      simpa only [mem_closedBall,dist_eq_norm] using hp.1
    have hz' : ‖p.2‖ ≤ 1 := by
      simpa only [mem_closedBall,dist_zero_right] using hp.2
    have hd : dist (p.1,r) (y0,(0 : ℝ)) ≤ ε/4 := by
      rw [dist_eq_norm]
      change max ‖p.1-y0‖ ‖r-(0 : ℝ)‖ ≤ ε/4
      rw [sub_zero,Real.norm_eq_abs]
      exact max_le (by linarith) (by linarith)
    exact (hG ((p.1,r),p.2) hd hz').comp (p,r) hc.contDiffAt
  have he : ∀ p ∈ s, centerSpatialRadius F =ᶠ[𝓝 (p,r)] centerSpatialRadius G := by
    intro p hp
    apply centerSpatialRadius_eventuallyEq_on_geometric_room F G ε hε y0 heq p.1 p.2 r
    · simpa only [mem_ball,dist_eq_norm] using hp.1
    · simpa only [mem_ball,dist_zero_right] using hp.2
    · exact hr
  have hclosed := parameterJetField_eq_on_set_of_local_eq j (centerSpatialRadius F)
    (centerSpatialRadius G) s t hst hts r
    (fun p _ => (contDiff_centerSpatialRadius F hF).contDiffAt) hlocalG he
  have hp : (y,z) ∈ t := by
    refine ⟨?_,?_⟩
    · simpa only [mem_closedBall,dist_eq_norm] using (by linarith : ‖y-y0‖ ≤ ε/8)
    · simpa only [mem_closedBall,dist_zero_right] using hz
  exact hclosed (y,z) hp

def RawCoefficientMixedJetIdentities (ε : ℝ) (y0 : R3)
    (H a G : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (R3 × ℝ) × R3 → ℝ) : Prop :=
  ∀ j : ℕ, ∀ y : R3, ‖y-y0‖ ≤ ε/16 → ∀ z : R3, ‖z‖ ≤ 1 →
    ∀ r : ℝ, |r| ≤ ε/16 →
      coefficientMixedJet j (fun p => H p - 1) ((y,z),r) =
        coefficientMixedJet j (fun p => G p - 1) ((y,z),r) ∧
      coefficientMixedJet j (fun p => a p - 1) ((y,z),r) =
        coefficientMixedJet j (fun p => matrixPrincipalCoefficient G p - 1) ((y,z),r) ∧
      coefficientMixedJet j (fun p => w p - 1) ((y,z),r) =
        coefficientMixedJet j (fun p => matrixVolumeDensity G p - 1) ((y,z),r)

theorem rawCoefficientMixedJetIdentities_of_geometric_room
    (H a G : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (R3 × ℝ) × R3 → ℝ)
    (hH : ContDiff ℝ ∞ H) (ha : ContDiff ℝ ∞ a) (hw : ContDiff ℝ ∞ w)
    (hG : ContDiff ℝ ∞ G) (hposH : ∀ p, (H p).PosDef)
    (ε : ℝ) (hε : 0 < ε) (y0 : R3)
    (heqH : ∀ p : (R3 × ℝ) × R3, dist p.1 (y0,0) ≤ ε/4 → ‖p.2‖ ≤ 1 → H p = G p)
    (heq : ∀ p : (R3 × ℝ) × R3, dist p.1 (y0,0) ≤ ε/4 → ‖p.2‖ ≤ 1 →
      a p = matrixPrincipalCoefficient G p ∧ w p = matrixVolumeDensity G p) :
    RawCoefficientMixedJetIdentities ε y0 H a G w := by
  have hposG : ∀ p : (R3 × ℝ) × R3, dist p.1 (y0,0) ≤ ε/4 → ‖p.2‖ ≤ 1 →
      (G p).PosDef := by
    intro p hp hz
    rw [← heqH p hp hz]
    exact hposH p
  have hsA : ∀ p : (R3 × ℝ) × R3, dist p.1 (y0,0) ≤ ε/4 → ‖p.2‖ ≤ 1 →
      ContDiffAt ℝ ∞ (matrixPrincipalCoefficient G) p := by
    intro p hp hz
    exact contDiffAt_matrixPrincipalCoefficient_of_posDef G p hG.contDiffAt (hposG p hp hz)
  have hsW : ∀ p : (R3 × ℝ) × R3, dist p.1 (y0,0) ≤ ε/4 → ‖p.2‖ ≤ 1 →
      ContDiffAt ℝ ∞ (matrixVolumeDensity G) p := by
    intro p hp hz
    exact contDiffAt_matrixVolumeDensity_of_posDef G p hG.contDiffAt (hposG p hp hz)
  intro j y hy z hz r hr
  refine ⟨?_,?_,?_⟩
  · exact coefficientMixedJet_eq_of_local_raw_smoothness
      (fun p => H p - 1) (fun p => G p - 1) (hH.sub contDiff_const) ε hε y0
      (fun p _ _ => hG.contDiffAt.sub contDiffAt_const)
      (fun p hp hz => congrArg (fun A => A-1) (heqH p hp hz)) j y z r hy hz hr
  · exact coefficientMixedJet_eq_of_local_raw_smoothness
      (fun p => a p - 1) (fun p => matrixPrincipalCoefficient G p - 1)
      (ha.sub contDiff_const) ε hε y0
      (fun p hp hz => (hsA p hp hz).sub contDiffAt_const)
      (fun p hp hz => congrArg (fun A => A-1) (heq p hp hz).1) j y z r hy hz hr
  · exact coefficientMixedJet_eq_of_local_raw_smoothness
      (fun p => w p - 1) (fun p => matrixVolumeDensity G p - 1)
      (hw.sub contDiff_const) ε hε y0
      (fun p hp hz => (hsW p hp hz).sub contDiffAt_const)
      (fun p hp hz => congrArg (fun A => A-1) (heq p hp hz).2) j y z r hy hz hr

theorem actualCoefficientMixedJetBounds_transfer
    (ε : ℝ) (y0 : R3)
    (H a G : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (R3 × ℝ) × R3 → ℝ)
    (heq : RawCoefficientMixedJetIdentities ε y0 H a G w)
    (hbound : ActualCoefficientMixedJetBounds ε y0 H a w) :
    ActualCoefficientMixedJetBounds ε y0 G (matrixPrincipalCoefficient G) (matrixVolumeDensity G) := by
  intro N
  obtain ⟨C,hC,hb⟩ := hbound N
  refine ⟨C,hC,?_⟩
  intro j hj y hy z hz r hr
  rcases heq j y hy z hz r hr with ⟨hH,ha,hw⟩
  rw [← hH,← ha,← hw]
  exact hb j hj y hy z hz r hr

end OAI.AnisotropicCalderon.MetricOperator
