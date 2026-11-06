import MixedKernelObservedOutputRooms
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.PhaseCoordinates
open Set Filter Metric
open scoped Topology ContDiff
def heightCutBetween (l h ε s : ℝ) : ℝ :=
  Real.smoothTransition ((s - (-l + 17 * ε / 8)) / (3 * ε / 4)) *
    (1 - Real.smoothTransition ((s - (h + 17 * ε / 8)) / (3 * ε / 4)))

theorem contDiff_heightCutBetween (l h ε : ℝ) : ContDiff ℝ ∞ (heightCutBetween l h ε) := by
  unfold heightCutBetween
  fun_prop

theorem heightCutBetween_ne_zero {l h ε s : ℝ} (hε : 0 < ε) (hz : heightCutBetween l h ε s ≠ 0) :
    -l + 17 * ε / 8 < s ∧ s < h + 23 * ε / 8 := by
  have hw : 0 < 3 * ε / 4 := by linarith
  unfold heightCutBetween at hz
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hz
  constructor
  · by_contra hs
    apply h1
    apply Real.smoothTransition.zero_of_nonpos
    rw [div_le_iff₀ hw]
    linarith [not_lt.mp hs]
  · by_contra hs
    apply h2
    have hA : Real.smoothTransition ((s - (h + 17 * ε / 8)) / (3 * ε / 4)) = 1 :=
      Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hw]; linarith [not_lt.mp hs])
    rw [hA, sub_self]

theorem heightCutBetween_eq_one {l h ε s : ℝ} (hε : 0 < ε) (h1 : -l + 23 * ε / 8 ≤ s)
    (h2 : s ≤ h + 17 * ε / 8) : heightCutBetween l h ε s = 1 := by
  have hw : 0 < 3 * ε / 4 := by linarith
  have hA : Real.smoothTransition ((s - (-l + 17 * ε / 8)) / (3 * ε / 4)) = 1 :=
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hw]; linarith)
  have hB : Real.smoothTransition ((s - (h + 17 * ε / 8)) / (3 * ε / 4)) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by rw [div_le_iff₀ hw]; linarith)
  unfold heightCutBetween
  rw [hA, hB]
  ring


variable {K : Type*} [NormedAddCommGroup K] {l h ε R : ℝ}

def suppBoxBetween (l h ε R : ℝ) : Set (ℝ × K) :=
  Icc (-l+17*ε/8) (h+23*ε/8) ×ˢ closedBall (0:K) (3*R/4)

def transLBetween (l h ε R : ℝ) : Set (ℝ × K) :=
  Icc (-l+17*ε/8) (h+23*ε/8) ×ˢ {z:K | R/2 ≤ ‖z‖ ∧ ‖z‖ ≤ 3*R/4}

theorem suppBoxBetween_subset_suppBox (hhl : h ≤ l) :
    (suppBoxBetween l h ε R : Set (ℝ × K)) ⊆ suppBox l ε R := by
  rintro ⟨s,z⟩ ⟨hs,hz⟩
  exact ⟨⟨hs.1,by linarith [hs.2]⟩,hz⟩

theorem closedO_subset_suppBoxBetween (heps : 0 < ε) (hl : 4*ε < l) (hR : 0 < R) :
    (closedO h ε R : Set (ℝ × K)) ⊆ suppBoxBetween l h ε R := by
  rintro ⟨s,z⟩ ⟨hs,hz⟩
  refine ⟨⟨by linarith [hs.1],by linarith [hs.2]⟩,?_⟩
  exact (closedBall_subset_closedBall (by linarith : R/2 ≤ 3*R/4)) hz

theorem mem_plateau_of_not_trans_between {y : ℝ × K} (hy : y ∈ suppBoxBetween l h ε R)
    (hn : y ∉ transB l ε R ∪ transT h ε R ∪ transLBetween l h ε R) :
    y ∈ Ioo (-l + 23 * ε / 8) (h + 17 * ε / 8) ×ˢ ball (0 : K) (R / 2) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hy
  rw [mem_closedBall_zero_iff] at h3
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · by_contra h
    exact hn (Or.inl (Or.inl ⟨⟨h1, not_lt.mp h⟩, mem_closedBall_zero_iff.mpr h3⟩))
  · by_contra h
    exact hn (Or.inl (Or.inr ⟨⟨not_lt.mp h, h2⟩, mem_closedBall_zero_iff.mpr h3⟩))
  · rw [mem_ball_zero_iff]
    by_contra h
    exact hn (Or.inr ⟨⟨h1, h2⟩, not_lt.mp h, h3⟩)

theorem roomFormula_mem_suppBoxBetween {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (theta : E → ℝ) (ell : E →L[ℝ] ℝ) (p : E) [CompleteSpace ell.ker] {l h ε R : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (x : E)
    (hx : heightCutBetween l h ε (theta x) *
      lateralCut R (‖ell.ker.orthogonalProjectionOnto (x - p)‖ ^ 2) ≠ 0) :
    (theta x, ell.ker.orthogonalProjectionOnto (x - p)) ∈ suppBoxBetween l h ε R := by
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hx
  have hs := heightCutBetween_ne_zero hε h1
  have hq := lateralCut_ne_zero hR h2
  refine ⟨⟨hs.1.le, hs.2.le⟩, ?_⟩
  rw [mem_closedBall_zero_iff]
  by_contra hn
  have hn' := not_le.mp hn
  nlinarith [mul_pos (sub_pos.mpr hn')
    (show 0 < ‖ell.ker.orthogonalProjectionOnto (x - p)‖ + 3 * R / 4 by
      linarith [norm_nonneg (ell.ker.orthogonalProjectionOnto (x - p))])]

theorem exists_room_cutoff_between {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hell : fderiv ℝ θ p ≠ 0) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker), p ∈ e.source ∧
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ Icc (-ρ) ρ ×ˢ closedBall (0 : (fderiv ℝ θ p).ker) ρ ⊆ e.target ∧
      ∀ l h ε R : ℝ, 0 < ε → 4 * ε < h → h ≤ l → 0 < R → l + 4 * ε ≤ ρ → R ≤ ρ →
        ∃ chi : R3 → ℝ, ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧
          tsupport chi ⊆ e.symm '' suppBoxBetween l h ε R ∧
          (∀ x ∈ e.symm '' closedO h ε R, chi x = 1) ∧
          (∀ x, x ∉ e.symm '' (transB l ε R ∪ transT h ε R ∪ transLBetween l h ε R) →
            chi =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) ∨ chi =ᶠ[𝓝 x] (fun _ => (1 : ℝ))) := by
  obtain ⟨e, hpe, he, ρ, hρ, hbox⟩ := exists_tangent_box_cutoff hθ p h0 hell
  have hBig := (hbox ρ ρ le_rfl hρ.le le_rfl).1
  refine ⟨e, hpe, he, ρ, hρ, hBig, fun l h ε R hε hh hhl hR hlρ hRρ => ?_⟩
  have hl : 4 * ε < l := hh.trans_le hhl
  have hSt : (suppBoxBetween l h ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target :=
    ((suppBoxBetween_subset_suppBox hhl).trans
      ((suppBox_subset_roomD hε hl hR).trans roomD_subset_closedD)).trans
      ((closedD_subset_big hε hlρ hRρ).trans hBig)
  obtain ⟨chi, hc, hcs, hts, hgerm, hzero⟩ := exists_chart_supported_cutoff e
    (isCompact_Icc.prod (isCompact_closedBall _ _)) hSt
    (fun y => heightCutBetween l h ε (θ y) *
      lateralCut R (‖(fderiv ℝ θ p).ker.orthogonalProjectionOnto (y - p)‖ ^ 2))
    (contDiff_tangent_formula hθ _ p (contDiff_heightCutBetween l h ε) (contDiff_lateralCut R))
    (fun x _ hx => by
      rw [he x]
      exact roomFormula_mem_suppBoxBetween θ _ p hε hR x hx)
  refine ⟨chi, hc, hcs, hts, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    have hyS : y ∈ suppBoxBetween l h ε R := closedO_subset_suppBoxBetween hε hl hR hy
    have hey : e (e.symm y) = y := e.right_inv (hSt hyS)
    rw [he] at hey
    have hs : θ (e.symm y) = y.1 := congrArg Prod.fst hey
    have hz : (fderiv ℝ θ p).ker.orthogonalProjectionOnto (e.symm y - p) = y.2 :=
      congrArg Prod.snd hey
    rw [(hgerm _ ⟨y, hyS, rfl⟩).eq_of_nhds]
    obtain ⟨⟨h1, h2⟩, h3⟩ := hy
    rw [mem_closedBall_zero_iff] at h3
    show heightCutBetween l h ε (θ (e.symm y)) *
      lateralCut R (‖(fderiv ℝ θ p).ker.orthogonalProjectionOnto (e.symm y - p)‖ ^ 2) = 1
    have hR2 : (0 : ℝ) ≤ R / 2 := by linarith
    have hmm := mul_le_mul h3 h3 (norm_nonneg _) hR2
    have hq : ‖y.2‖ ^ 2 ≤ R ^ 2 / 4 := by nlinarith
    have ha1 : -l + 23 * ε / 8 ≤ y.1 := by linarith
    have ha2 : y.1 ≤ h + 17 * ε / 8 := by linarith
    rw [hs, hz, heightCutBetween_eq_one hε ha1 ha2, lateralCut_eq_one hR hq, mul_one]
  · intro x hx
    by_cases hxK : x ∈ e.symm '' suppBoxBetween l h ε R
    · right
      obtain ⟨y, hy, rfl⟩ := hxK
      have hyt := hSt hy
      have hxs : e.symm y ∈ e.source := e.map_target hyt
      have hey : e (e.symm y) = y := e.right_inv hyt
      have hyV := mem_plateau_of_not_trans_between hy (fun h => hx ⟨y, h, rfl⟩)
      have hV : e.source ∩ e ⁻¹' (Ioo (-l + 23 * ε / 8) (h + 17 * ε / 8) ×ˢ
          ball (0 : (fderiv ℝ θ p).ker) (R / 2)) ∈ 𝓝 (e.symm y) :=
        (e.isOpen_inter_preimage (isOpen_Ioo.prod isOpen_ball)).mem_nhds
          ⟨hxs, by rw [mem_preimage, hey]; exact hyV⟩
      filter_upwards [hV, hgerm _ ⟨y, hy, rfl⟩] with z hz hzF
      rw [hzF]
      have hz2 := hz.2
      simp only [mem_preimage, he z, Set.mem_prod, Set.mem_Ioo, mem_ball_zero_iff] at hz2
      obtain ⟨⟨h1, h2⟩, h3⟩ := hz2
      show heightCutBetween l h ε (θ z) *
        lateralCut R (‖(fderiv ℝ θ p).ker.orthogonalProjectionOnto (z - p)‖ ^ 2) = 1
      have hR2 : (0 : ℝ) ≤ R / 2 := by linarith
      have hmm := mul_le_mul h3.le h3.le (norm_nonneg _) hR2
      have hq : ‖(fderiv ℝ θ p).ker.orthogonalProjectionOnto (z - p)‖ ^ 2 ≤ R ^ 2 / 4 := by
        nlinarith
      rw [heightCutBetween_eq_one hε h1.le h2.le, lateralCut_eq_one hR hq, mul_one]
    · left
      exact hzero x hxK


end OAI.AnisotropicCalderon.PhaseCoordinates
end
