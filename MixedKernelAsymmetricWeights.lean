import MixedKernelAsymmetricCutoff
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Filter Metric PhaseCoordinates
open scoped Topology ContDiff

theorem strictPhase_height_bounds_between {k l h eps : ℝ}
    (hk : 0 < k) (heps : 0 < eps) (hh : 4*eps < h) (hhl : h ≤ l)
    (hkh : k*(l+4*eps) < 1/4) :
    (∀ s, -l ≤ s → s ≤ -l+23*eps/8 → strictHeight k s ≤ strictHeight k (-l+3*eps)) ∧
    (∀ s, -l ≤ s → s ≤ h+23*eps/8 → strictHeight k s ≤ strictHeight k (h+3*eps)) ∧
    (∀ s, -eps ≤ s → s ≤ h+4*eps → strictHeight k (-eps) ≤ strictHeight k s) := by
  have hl : 4*eps < l := hh.trans_le hhl
  obtain ⟨hB,_,hO⟩ := strictPhase_height_bounds hk heps hl hkh
  have hb : l+4*eps < 1/(4*k) := by
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 4*k)]
    linarith
  have hm := (strictPhaseProfile_strictMonoOn hk).monotoneOn
  have hI : ∀ t, -l ≤ t → t ≤ l+4*eps → t ∈ Icc (-(1/(4*k))) (1/(4*k)) :=
    fun t h1 h2 => ⟨by linarith,by linarith⟩
  refine ⟨hB,fun s h1 h2 => ?_,fun s h1 h2 => hO s h1 (by linarith)⟩
  exact hm (hI s h1 (by linarith)) (hI (h+3*eps) (by linarith) (by linarith)) (by linarith)

theorem native_weight_heights_between {K : Type*} [NormedAddCommGroup K]
    (e : OpenPartialHomeomorph R3 (ℝ × K)) {theta : R3 → ℝ} {P : R3 → K} {p : R3}
    (he : ∀ x, e x = (theta x,P (x-p))) {l h eps R k : ℝ}
    (hk : 0 < k) (heps : 0 < eps) (hh : 4*eps < h) (hhl : h ≤ l) (hR : 0 < R)
    (hkh : k*(l+4*eps) < 1/4) (hDt : closedD l eps R ⊆ e.target) :
    (∀ x ∈ e.symm '' transB l eps R,
      strictHeight k (theta x) ≤ strictHeight k (-l+3*eps)) ∧
    (∀ x ∈ e.symm '' (transT h eps R ∪ transLBetween l h eps R),
      strictHeight k (theta x) ≤ strictHeight k (h+3*eps)) ∧
    (∀ x ∈ e.symm '' closedO h eps R,
      strictHeight k (-eps) ≤ strictHeight k (theta x)) := by
  have hl : 4*eps < l := hh.trans_le hhl
  have htheta : ∀ y ∈ (closedD l eps R : Set (ℝ × K)), theta (e.symm y) = y.1 := by
    intro y hy
    have h := e.right_inv (hDt hy)
    rw [he] at h
    exact congrArg Prod.fst h
  have hTD : (transT h eps R : Set (ℝ × K)) ⊆ closedD l eps R := by
    rintro ⟨s,z⟩ ⟨hs,hz⟩
    exact ⟨⟨by linarith [hs.1],by linarith [hs.2]⟩,
      (closedBall_subset_closedBall (by linarith : 3*R/4 ≤ R)) hz⟩
  have hLD : (transLBetween l h eps R : Set (ℝ × K)) ⊆ closedD l eps R := by
    rintro ⟨s,z⟩ ⟨hs,hz⟩
    refine ⟨⟨by linarith [hs.1],by linarith [hs.2]⟩,?_⟩
    rw [mem_closedBall_zero_iff]
    linarith [hz.2]
  have hOD : (closedO h eps R : Set (ℝ × K)) ⊆ closedD l eps R :=
    (closedO_subset_suppBoxBetween heps hl hR).trans
      ((suppBoxBetween_subset_suppBox hhl).trans
        ((suppBox_subset_roomD heps hl hR).trans roomD_subset_closedD))
  obtain ⟨hB,hH,hO⟩ := strictPhase_height_bounds_between hk heps hh hhl hkh
  refine ⟨?_,?_,?_⟩
  · rintro x ⟨y,hy,rfl⟩
    rw [htheta y ((transB_subset_roomD heps hl hR).trans roomD_subset_closedD hy)]
    exact hB y.1 (by linarith [hy.1.1]) hy.1.2
  · rintro x ⟨y,hy,rfl⟩
    rcases hy with hy | hy
    · rw [htheta y (hTD hy)]
      exact hH y.1 (by linarith [hy.1.1]) hy.1.2
    · rw [htheta y (hLD hy)]
      exact hH y.1 (by linarith [hy.1.1]) hy.1.2
  · rintro x ⟨y,hy,rfl⟩
    rw [htheta y (hOD hy)]
    exact hO y.1 hy.1.1 (by linarith [hy.1.2])

/-- Actual open data rooms and compact interior residual buffers for the new cutoff. -/
theorem native_rooms_between {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] [ProperSpace K]
    (e : OpenPartialHomeomorph R3 (ℝ × K)) {l h eps R : ℝ}
    (heps : 0 < eps) (hh : 4*eps < h) (hhl : h ≤ l) (hR : 0 < R)
    (hDt : closedD l eps R ⊆ e.target) :
    IsOpen (e.symm '' roomD l eps R) ∧ IsOpen (e.symm '' roomO h eps R) ∧
    IsOpen (e.symm '' (roomStop h eps R ∪ roomSlat l eps R)) ∧
    (e.symm '' (roomStop h eps R ∪ roomSlat l eps R)).Nonempty ∧
    e.symm '' roomO h eps R ⊆ e.symm '' roomD l eps R ∧
    e.symm '' (roomStop h eps R ∪ roomSlat l eps R) ⊆ e.symm '' roomD l eps R ∧
    IsCompact (e.symm '' transB l eps R) ∧ e.symm '' transB l eps R ⊆ e.symm '' roomD l eps R ∧
    IsCompact (e.symm '' (transT h eps R ∪ transLBetween l h eps R)) ∧
    e.symm '' (transT h eps R ∪ transLBetween l h eps R) ⊆
      e.symm '' (roomStop h eps R ∪ roomSlat l eps R) ∧
    IsCompact (e.symm '' closedO h eps R) ∧ e.symm '' closedO h eps R ⊆ e.symm '' roomD l eps R ∧
    IsCompact (e.symm '' (closedStop h eps R ∪ closedSlat l eps R)) ∧
    e.symm '' (roomStop h eps R ∪ roomSlat l eps R) ⊆
      e.symm '' (closedStop h eps R ∪ closedSlat l eps R) ∧
    e.symm '' (closedStop h eps R ∪ closedSlat l eps R) ⊆ e.symm '' roomD l eps R := by
  have hl : 4*eps < l := hh.trans_le hhl
  have hStopD : (closedStop h eps R : Set (ℝ × K)) ⊆ roomD l eps R := by
    rintro ⟨s,z⟩ ⟨hs,hz⟩
    refine ⟨⟨by linarith [hs.1],by linarith [hs.2]⟩,?_⟩
    rw [mem_ball_zero_iff]
    have hz' := mem_closedBall_zero_iff.mp hz
    linarith
  have hObsD : (closedStop h eps R ∪ closedSlat l eps R : Set (ℝ × K)) ⊆ roomD l eps R :=
    union_subset hStopD (closedSlat_subset_roomD heps hl hR)
  have hObs : (roomStop h eps R ∪ roomSlat l eps R : Set (ℝ × K)) ⊆
      closedStop h eps R ∪ closedSlat l eps R :=
    union_subset_union roomStop_subset_closedStop roomSlat_subset_closedSlat
  have hOD : (closedO h eps R : Set (ℝ × K)) ⊆ roomD l eps R :=
    (closedO_subset_suppBoxBetween heps hl hR).trans
      ((suppBoxBetween_subset_suppBox hhl).trans (suppBox_subset_roomD heps hl hR))
  have hHS : (transT h eps R ∪ transLBetween l h eps R : Set (ℝ × K)) ⊆
      roomStop h eps R ∪ roomSlat l eps R := by
    intro y hy
    rcases hy with hy | hy
    · exact Or.inl (transT_subset_roomStop heps hR hy)
    · apply Or.inr
      apply transL_subset_roomSlat heps hR
      exact ⟨⟨hy.1.1,by linarith [hy.1.2]⟩,hy.2⟩
  have hBtarget : (transB l eps R : Set (ℝ × K)) ⊆ e.target :=
    (transB_subset_roomD heps hl hR).trans (roomD_subset_closedD.trans hDt)
  have hHtarget : (transT h eps R ∪ transLBetween l h eps R : Set (ℝ × K)) ⊆ e.target :=
    hHS.trans (hObs.trans (hObsD.trans (roomD_subset_closedD.trans hDt)))
  have hOtarget : (closedO h eps R : Set (ℝ × K)) ⊆ e.target :=
    hOD.trans (roomD_subset_closedD.trans hDt)
  have hObstarget : (closedStop h eps R ∪ closedSlat l eps R : Set (ℝ × K)) ⊆ e.target :=
    hObsD.trans (roomD_subset_closedD.trans hDt)
  have hcB : IsCompact (transB l eps R : Set (ℝ × K)) := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hcH : IsCompact (transT h eps R ∪ transLBetween l h eps R : Set (ℝ × K)) :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).union (isCompact_Icc.prod (isCompact_annulus _ _))
  have hcO : IsCompact (closedO h eps R : Set (ℝ × K)) := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hcObs : IsCompact (closedStop h eps R ∪ closedSlat l eps R : Set (ℝ × K)) :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).union (isCompact_Icc.prod (isCompact_annulus _ _))
  have hOpO : IsOpen (roomO h eps R : Set (ℝ × K)) := isOpen_Ioo.prod isOpen_ball
  have hOpS : IsOpen (roomStop h eps R ∪ roomSlat l eps R : Set (ℝ × K)) :=
    (isOpen_Ioo.prod isOpen_ball).union
      (isOpen_Ioo.prod ((isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)))
  refine ⟨e.isOpen_image_symm_of_subset_target (isOpen_Ioo.prod isOpen_ball)
      (roomD_subset_closedD.trans hDt),
    e.isOpen_image_symm_of_subset_target hOpO (roomO_subset_closedO.trans hOtarget),
    e.isOpen_image_symm_of_subset_target hOpS (hObs.trans hObstarget),?_,
    image_mono (roomO_subset_closedO.trans hOD),image_mono (hObs.trans hObsD),
    hcB.image_of_continuousOn (e.continuousOn_symm.mono hBtarget),image_mono (transB_subset_roomD heps hl hR),
    hcH.image_of_continuousOn (e.continuousOn_symm.mono hHtarget),image_mono hHS,
    hcO.image_of_continuousOn (e.continuousOn_symm.mono hOtarget),image_mono hOD,
    hcObs.image_of_continuousOn (e.continuousOn_symm.mono hObstarget),image_mono hObs,image_mono hObsD⟩
  exact ⟨e.symm (h+eps,0),mem_image_of_mem _
    (Or.inl ⟨⟨by linarith,by linarith⟩,mem_ball_self (by positivity)⟩)⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
