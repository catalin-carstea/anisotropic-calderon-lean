import Calderon.MixedKernelConstruction.MixedKernelRoomParametersV021
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.PhaseCoordinates
section Rooms
variable {K : Type*} [NormedAddCommGroup K]

/-- R3/R5/R6: coordinate rooms, closures, support box and closed transition sets. -/
def roomD (l ε R : ℝ) : Set (ℝ × K) := Ioo (-l) (l + 4 * ε) ×ˢ ball (0 : K) R
def closedD (l ε R : ℝ) : Set (ℝ × K) := Icc (-l) (l + 4 * ε) ×ˢ closedBall (0 : K) R
def roomO (l ε R : ℝ) : Set (ℝ × K) := Ioo (-ε) (l + 3 * ε / 2) ×ˢ ball (0 : K) (R / 2)
def closedO (l ε R : ℝ) : Set (ℝ × K) := Icc (-ε) (l + 3 * ε / 2) ×ˢ closedBall (0 : K) (R / 2)
def roomT (l ε R : ℝ) : Set (ℝ × K) :=
  Ioo (l + 9 * ε / 8) (l + 11 * ε / 8) ×ˢ ball (0 : K) (R / 4)
def closedT (l ε R : ℝ) : Set (ℝ × K) :=
  Icc (l + 9 * ε / 8) (l + 11 * ε / 8) ×ˢ closedBall (0 : K) (R / 4)
def roomStop (l ε R : ℝ) : Set (ℝ × K) :=
  Ioo (l + ε / 2) (l + 7 * ε / 2) ×ˢ ball (0 : K) (7 * R / 8)
def closedStop (l ε R : ℝ) : Set (ℝ × K) :=
  Icc (l + ε / 2) (l + 7 * ε / 2) ×ˢ closedBall (0 : K) (7 * R / 8)
def roomSlat (l ε R : ℝ) : Set (ℝ × K) :=
  Ioo (-l + ε) (l + 7 * ε / 2) ×ˢ {z : K | R / 3 < ‖z‖ ∧ ‖z‖ < 7 * R / 8}
def closedSlat (l ε R : ℝ) : Set (ℝ × K) :=
  Icc (-l + ε) (l + 7 * ε / 2) ×ˢ {z : K | R / 3 ≤ ‖z‖ ∧ ‖z‖ ≤ 7 * R / 8}
def suppBox (l ε R : ℝ) : Set (ℝ × K) :=
  Icc (-l + 17 * ε / 8) (l + 23 * ε / 8) ×ˢ closedBall (0 : K) (3 * R / 4)
def transB (l ε R : ℝ) : Set (ℝ × K) :=
  Icc (-l + 17 * ε / 8) (-l + 23 * ε / 8) ×ˢ closedBall (0 : K) (3 * R / 4)
def transT (l ε R : ℝ) : Set (ℝ × K) :=
  Icc (l + 17 * ε / 8) (l + 23 * ε / 8) ×ˢ closedBall (0 : K) (3 * R / 4)
def transL (l ε R : ℝ) : Set (ℝ × K) :=
  Icc (-l + 17 * ε / 8) (l + 23 * ε / 8) ×ˢ {z : K | R / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 * R / 4}

macro "room_le" : tactic => `(tactic| (
  intro y hy
  simp only [roomD, closedD, roomO, closedO, roomT, closedT, roomStop, closedStop, roomSlat,
    closedSlat, suppBox, transB, transT, transL, Set.mem_prod, Set.mem_Icc, Set.mem_Ioo,
    mem_closedBall_zero_iff, mem_ball_zero_iff, Set.mem_setOf_eq] at hy ⊢
  casesm* _ ∧ _
  constructorm* _ ∧ _ <;> linarith))

variable {l ε R : ℝ}

theorem roomD_subset_closedD : (roomD l ε R : Set (ℝ × K)) ⊆ closedD l ε R := by room_le
theorem closedD_subset_big {ρ : ℝ} (hε : 0 < ε) (hlρ : l + 4 * ε ≤ ρ) (hRρ : R ≤ ρ) :
    (closedD l ε R : Set (ℝ × K)) ⊆ Icc (-ρ) ρ ×ˢ closedBall (0 : K) ρ := by room_le
theorem closedO_subset_roomD (hε : 0 < ε) (hl : 4 * ε < l) (hR : 0 < R) :
    (closedO l ε R : Set (ℝ × K)) ⊆ roomD l ε R := by room_le
theorem roomO_subset_closedO : (roomO l ε R : Set (ℝ × K)) ⊆ closedO l ε R := by room_le
theorem closedT_subset_roomO (hε : 0 < ε) (hl : 4 * ε < l) (hR : 0 < R) :
    (closedT l ε R : Set (ℝ × K)) ⊆ roomO l ε R := by room_le
theorem roomT_subset_closedT : (roomT l ε R : Set (ℝ × K)) ⊆ closedT l ε R := by room_le
theorem closedT_subset_roomStop (hε : 0 < ε) (hR : 0 < R) :
    (closedT l ε R : Set (ℝ × K)) ⊆ roomStop l ε R := by room_le
theorem roomStop_subset_closedStop : (roomStop l ε R : Set (ℝ × K)) ⊆ closedStop l ε R := by
  room_le
theorem closedStop_subset_roomD (hε : 0 < ε) (hl : 4 * ε < l) (hR : 0 < R) :
    (closedStop l ε R : Set (ℝ × K)) ⊆ roomD l ε R := by room_le
theorem roomSlat_subset_closedSlat : (roomSlat l ε R : Set (ℝ × K)) ⊆ closedSlat l ε R := by
  room_le
theorem closedSlat_subset_roomD (hε : 0 < ε) (hl : 4 * ε < l) (hR : 0 < R) :
    (closedSlat l ε R : Set (ℝ × K)) ⊆ roomD l ε R := by room_le
theorem transB_subset_roomD (hε : 0 < ε) (hl : 4 * ε < l) (hR : 0 < R) :
    (transB l ε R : Set (ℝ × K)) ⊆ roomD l ε R := by room_le
theorem transT_subset_roomStop (hε : 0 < ε) (hR : 0 < R) :
    (transT l ε R : Set (ℝ × K)) ⊆ roomStop l ε R := by room_le
theorem transL_subset_roomSlat (hε : 0 < ε) (hR : 0 < R) :
    (transL l ε R : Set (ℝ × K)) ⊆ roomSlat l ε R := by room_le
theorem suppBox_subset_roomD (hε : 0 < ε) (hl : 4 * ε < l) (hR : 0 < R) :
    (suppBox l ε R : Set (ℝ × K)) ⊆ roomD l ε R := by room_le
theorem closedO_subset_suppBox (hε : 0 < ε) (hl : 4 * ε < l) (hR : 0 < R) :
    (closedO l ε R : Set (ℝ × K)) ⊆ suppBox l ε R := by room_le

/-- R5: a support-box point off the closed transition union lies in the open plateau. -/
theorem mem_plateau_of_not_trans {y : ℝ × K} (hy : y ∈ suppBox l ε R)
    (hn : y ∉ transB l ε R ∪ transT l ε R ∪ transL l ε R) :
    y ∈ Ioo (-l + 23 * ε / 8) (l + 17 * ε / 8) ×ˢ ball (0 : K) (R / 2) := by
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

theorem isCompact_annulus [ProperSpace K] (r1 r2 : ℝ) :
    IsCompact {z : K | r1 ≤ ‖z‖ ∧ ‖z‖ ≤ r2} :=
  (isCompact_closedBall (0 : K) r2).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
    (fun _ hz => mem_closedBall_zero_iff.mpr hz.2)

end Rooms

/-- R6: closures of lifted coordinate rooms are compact and lie in the lifted closed set. -/
theorem room_closure {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {U C : Set Y} (hUC : U ⊆ C) (hC : IsCompact C)
    (hCt : C ⊆ e.target) :
    IsCompact (closure (e.symm '' U)) ∧ closure (e.symm '' U) ⊆ e.symm '' C := by
  have hK : IsCompact (e.symm '' C) := hC.image_of_continuousOn (e.continuousOn_symm.mono hCt)
  have hsub : closure (e.symm '' U) ⊆ e.symm '' C :=
    closure_minimal (image_mono hUC) hK.isClosed
  exact ⟨hK.of_isClosed_subset isClosed_closure hsub, hsub⟩

/-- R6: the native rooms `D, O, S = S_top ∪ S_lat, T`, their closures and the two
compact collars `e⁻¹ KB ⊆ D`, `e⁻¹ (KT ∪ KL) ⊆ S`. -/
theorem native_rooms {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] [ProperSpace K]
    (e : OpenPartialHomeomorph R3 (ℝ × K)) {ρ l ε R : ℝ}
    (hBig : Icc (-ρ) ρ ×ˢ closedBall (0 : K) ρ ⊆ e.target) (hε : 0 < ε) (hl : 4 * ε < l)
    (hR : 0 < R) (hlρ : l + 4 * ε ≤ ρ) (hRρ : R ≤ ρ) :
    IsOpen (e.symm '' roomD l ε R) ∧ IsOpen (e.symm '' roomO l ε R) ∧
    IsOpen (e.symm '' (roomStop l ε R ∪ roomSlat l ε R)) ∧ IsOpen (e.symm '' roomT l ε R) ∧
    (e.symm '' roomT l ε R).Nonempty ∧ IsPreconnected (e.symm '' roomD l ε R) ∧
    IsCompact (closure (e.symm '' roomD l ε R)) ∧
    IsCompact (closure (e.symm '' roomO l ε R)) ∧
    closure (e.symm '' roomO l ε R) ⊆ e.symm '' roomD l ε R ∧
    IsCompact (closure (e.symm '' (roomStop l ε R ∪ roomSlat l ε R))) ∧
    closure (e.symm '' (roomStop l ε R ∪ roomSlat l ε R)) ⊆ e.symm '' roomD l ε R ∧
    closure (e.symm '' roomT l ε R) ⊆ e.symm '' roomO l ε R ∧
    closure (e.symm '' roomT l ε R) ⊆ e.symm '' (roomStop l ε R ∪ roomSlat l ε R) ∧
    IsCompact (e.symm '' transB l ε R) ∧ e.symm '' transB l ε R ⊆ e.symm '' roomD l ε R ∧
    IsCompact (e.symm '' (transT l ε R ∪ transL l ε R)) ∧
    e.symm '' (transT l ε R ∪ transL l ε R) ⊆ e.symm '' (roomStop l ε R ∪ roomSlat l ε R) ∧
    IsCompact (e.symm '' suppBox l ε R) ∧ e.symm '' suppBox l ε R ⊆ e.symm '' roomD l ε R := by
  have hDt : (closedD l ε R : Set (ℝ × K)) ⊆ e.target :=
    (closedD_subset_big hε hlρ hRρ).trans hBig
  have hD : (roomD l ε R : Set (ℝ × K)) ⊆ closedD l ε R := roomD_subset_closedD
  have hOD : (closedO l ε R : Set (ℝ × K)) ⊆ roomD l ε R := closedO_subset_roomD hε hl hR
  have hTO : (closedT l ε R : Set (ℝ × K)) ⊆ roomO l ε R := closedT_subset_roomO hε hl hR
  have hTS : (closedT l ε R : Set (ℝ × K)) ⊆ roomStop l ε R := closedT_subset_roomStop hε hR
  have hStD : (closedStop l ε R : Set (ℝ × K)) ⊆ roomD l ε R := closedStop_subset_roomD hε hl hR
  have hSlD : (closedSlat l ε R : Set (ℝ × K)) ⊆ roomD l ε R := closedSlat_subset_roomD hε hl hR
  have hBD : (transB l ε R : Set (ℝ × K)) ⊆ roomD l ε R := transB_subset_roomD hε hl hR
  have hTTS : (transT l ε R : Set (ℝ × K)) ⊆ roomStop l ε R := transT_subset_roomStop hε hR
  have hLS : (transL l ε R : Set (ℝ × K)) ⊆ roomSlat l ε R := transL_subset_roomSlat hε hR
  have hSuD : (suppBox l ε R : Set (ℝ × K)) ⊆ roomD l ε R := suppBox_subset_roomD hε hl hR
  have hcD : IsCompact (closedD l ε R : Set (ℝ × K)) := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hcO : IsCompact (closedO l ε R : Set (ℝ × K)) := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hcT : IsCompact (closedT l ε R : Set (ℝ × K)) := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hcSt : IsCompact (closedStop l ε R : Set (ℝ × K)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hcSl : IsCompact (closedSlat l ε R : Set (ℝ × K)) := isCompact_Icc.prod (isCompact_annulus _ _)
  have hcB : IsCompact (transB l ε R : Set (ℝ × K)) := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hcTT : IsCompact (transT l ε R : Set (ℝ × K)) := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hcL : IsCompact (transL l ε R : Set (ℝ × K)) := isCompact_Icc.prod (isCompact_annulus _ _)
  have hcSu : IsCompact (suppBox l ε R : Set (ℝ × K)) := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hOt : (closedO l ε R : Set (ℝ × K)) ⊆ e.target := (hOD.trans hD).trans hDt
  have hTt : (closedT l ε R : Set (ℝ × K)) ⊆ e.target :=
    (hTO.trans roomO_subset_closedO).trans hOt
  have hStt : (closedStop l ε R : Set (ℝ × K)) ⊆ e.target := (hStD.trans hD).trans hDt
  have hSlt : (closedSlat l ε R : Set (ℝ × K)) ⊆ e.target := (hSlD.trans hD).trans hDt
  have hBt : (transB l ε R : Set (ℝ × K)) ⊆ e.target := (hBD.trans hD).trans hDt
  have hTTt : (transT l ε R : Set (ℝ × K)) ⊆ e.target :=
    (hTTS.trans roomStop_subset_closedStop).trans hStt
  have hLt : (transL l ε R : Set (ℝ × K)) ⊆ e.target :=
    (hLS.trans roomSlat_subset_closedSlat).trans hSlt
  have hSut : (suppBox l ε R : Set (ℝ × K)) ⊆ e.target := (hSuD.trans hD).trans hDt
  obtain ⟨hcO', hO'⟩ := room_closure e roomO_subset_closedO hcO hOt
  obtain ⟨hcS', hS'⟩ := room_closure e
    (union_subset_union roomStop_subset_closedStop roomSlat_subset_closedSlat)
    (hcSt.union hcSl) (union_subset hStt hSlt)
  obtain ⟨-, hT'⟩ := room_closure e roomT_subset_closedT hcT hTt
  obtain ⟨hcD', -⟩ := room_closure e hD hcD hDt
  have hoD : IsOpen (roomD l ε R : Set (ℝ × K)) := by
    unfold roomD; exact isOpen_Ioo.prod isOpen_ball
  have hoO : IsOpen (roomO l ε R : Set (ℝ × K)) := by
    unfold roomO; exact isOpen_Ioo.prod isOpen_ball
  have hoT : IsOpen (roomT l ε R : Set (ℝ × K)) := by
    unfold roomT; exact isOpen_Ioo.prod isOpen_ball
  have hoSt : IsOpen (roomStop l ε R : Set (ℝ × K)) := by
    unfold roomStop; exact isOpen_Ioo.prod isOpen_ball
  have hoSl : IsOpen (roomSlat l ε R : Set (ℝ × K)) := by
    unfold roomSlat
    exact isOpen_Ioo.prod ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const))
  have hpc : IsPreconnected (e.symm '' roomD l ε R) := by
    have h0 : IsPreconnected (roomD l ε R : Set (ℝ × K)) := by
      unfold roomD
      exact isPreconnected_Ioo.prod (convex_ball (0 : K) R).isPreconnected
    exact h0.image _ (e.continuousOn_symm.mono (hD.trans hDt))
  have hne : (e.symm '' roomT l ε R).Nonempty := by
    refine ⟨e.symm (l + 5 * ε / 4, 0), (l + 5 * ε / 4, 0), ?_, rfl⟩
    simp only [roomT, Set.mem_prod, Set.mem_Ioo, mem_ball_zero_iff, norm_zero]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> linarith
  refine ⟨e.isOpen_image_symm_of_subset_target hoD (hD.trans hDt),
    e.isOpen_image_symm_of_subset_target hoO ((roomO_subset_closedO).trans hOt),
    e.isOpen_image_symm_of_subset_target (hoSt.union hoSl)
      (union_subset (roomStop_subset_closedStop.trans hStt) (roomSlat_subset_closedSlat.trans hSlt)),
    e.isOpen_image_symm_of_subset_target hoT (roomT_subset_closedT.trans hTt),
    hne, hpc, hcD', hcO', hO'.trans (image_mono hOD), hcS',
    hS'.trans (image_mono (union_subset hStD hSlD)), hT'.trans (image_mono hTO),
    hT'.trans (image_mono (hTS.trans subset_union_left)),
    hcB.image_of_continuousOn (e.continuousOn_symm.mono hBt), image_mono hBD,
    (hcTT.union hcL).image_of_continuousOn (e.continuousOn_symm.mono (union_subset hTTt hLt)),
    image_mono (union_subset_union hTTS hLS),
    hcSu.image_of_continuousOn (e.continuousOn_symm.mono hSut), image_mono hSuD⟩

/-- R3: the global formula has nonzero values only over the ASYMMETRIC support box. -/
theorem roomFormula_mem_suppBox {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (theta : E → ℝ) (ell : E →L[ℝ] ℝ) (p : E) [CompleteSpace ell.ker] {l ε R : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (x : E)
    (hx : heightCut l ε (theta x) *
      lateralCut R (‖ell.ker.orthogonalProjectionOnto (x - p)‖ ^ 2) ≠ 0) :
    (theta x, ell.ker.orthogonalProjectionOnto (x - p)) ∈ suppBox l ε R := by
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hx
  have hs := heightCut_ne_zero hε h1
  have hq := lateralCut_ne_zero hR h2
  refine ⟨⟨hs.1.le, hs.2.le⟩, ?_⟩
  rw [mem_closedBall_zero_iff]
  by_contra hn
  have hn' := not_le.mp hn
  nlinarith [mul_pos (sub_pos.mpr hn')
    (show 0 < ‖ell.ker.orthogonalProjectionOnto (x - p)‖ + 3 * R / 4 by
      linarith [norm_nonneg (ell.ker.orthogonalProjectionOnto (x - p))])]

/-- R3–R5 on the ACTUAL tangent chart: the asymmetric-box cutoff, `χ = 1` pointwise on
the lifted closure of `O`, and the zero-or-one germ dichotomy off the lifted closed
transition union. -/
theorem exists_room_cutoff {θ : R3 → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : R3) (h0 : θ p = 0)
    (hell : fderiv ℝ θ p ≠ 0) :
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker), p ∈ e.source ∧
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ Icc (-ρ) ρ ×ˢ closedBall (0 : (fderiv ℝ θ p).ker) ρ ⊆ e.target ∧
      ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R → l + 4 * ε ≤ ρ → R ≤ ρ →
        ∃ chi : R3 → ℝ, ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧
          tsupport chi ⊆ e.symm '' suppBox l ε R ∧
          (∀ x ∈ e.symm '' closedO l ε R, chi x = 1) ∧
          (∀ x, x ∉ e.symm '' (transB l ε R ∪ transT l ε R ∪ transL l ε R) →
            chi =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) ∨ chi =ᶠ[𝓝 x] (fun _ => (1 : ℝ))) := by
  obtain ⟨e, hpe, he, ρ, hρ, hbox⟩ := exists_tangent_box_cutoff hθ p h0 hell
  have hBig := (hbox ρ ρ le_rfl hρ.le le_rfl).1
  refine ⟨e, hpe, he, ρ, hρ, hBig, fun l ε R hε hl hR hlρ hRρ => ?_⟩
  have hSt : (suppBox l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target :=
    ((suppBox_subset_roomD hε hl hR).trans roomD_subset_closedD).trans
      ((closedD_subset_big hε hlρ hRρ).trans hBig)
  obtain ⟨chi, hc, hcs, hts, hgerm, hzero⟩ := exists_chart_supported_cutoff e
    (isCompact_Icc.prod (isCompact_closedBall _ _)) hSt
    (fun y => heightCut l ε (θ y) *
      lateralCut R (‖(fderiv ℝ θ p).ker.orthogonalProjectionOnto (y - p)‖ ^ 2))
    (contDiff_tangent_formula hθ _ p (contDiff_heightCut l ε) (contDiff_lateralCut R))
    (fun x _ hx => by
      rw [he x]
      exact roomFormula_mem_suppBox θ _ p hε hR x hx)
  refine ⟨chi, hc, hcs, hts, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    have hyS : y ∈ suppBox l ε R := closedO_subset_suppBox hε hl hR hy
    have hey : e (e.symm y) = y := e.right_inv (hSt hyS)
    rw [he] at hey
    have hs : θ (e.symm y) = y.1 := congrArg Prod.fst hey
    have hz : (fderiv ℝ θ p).ker.orthogonalProjectionOnto (e.symm y - p) = y.2 :=
      congrArg Prod.snd hey
    rw [(hgerm _ ⟨y, hyS, rfl⟩).eq_of_nhds]
    obtain ⟨⟨h1, h2⟩, h3⟩ := hy
    rw [mem_closedBall_zero_iff] at h3
    show heightCut l ε (θ (e.symm y)) *
      lateralCut R (‖(fderiv ℝ θ p).ker.orthogonalProjectionOnto (e.symm y - p)‖ ^ 2) = 1
    have hR2 : (0 : ℝ) ≤ R / 2 := by linarith
    have hmm := mul_le_mul h3 h3 (norm_nonneg _) hR2
    have hq : ‖y.2‖ ^ 2 ≤ R ^ 2 / 4 := by nlinarith
    have ha1 : -l + 23 * ε / 8 ≤ y.1 := by linarith
    have ha2 : y.1 ≤ l + 17 * ε / 8 := by linarith
    rw [hs, hz, heightCut_eq_one hε ha1 ha2, lateralCut_eq_one hR hq, mul_one]
  · intro x hx
    by_cases hxK : x ∈ e.symm '' suppBox l ε R
    · right
      obtain ⟨y, hy, rfl⟩ := hxK
      have hyt := hSt hy
      have hxs : e.symm y ∈ e.source := e.map_target hyt
      have hey : e (e.symm y) = y := e.right_inv hyt
      have hyV := mem_plateau_of_not_trans hy (fun h => hx ⟨y, h, rfl⟩)
      have hV : e.source ∩ e ⁻¹' (Ioo (-l + 23 * ε / 8) (l + 17 * ε / 8) ×ˢ
          ball (0 : (fderiv ℝ θ p).ker) (R / 2)) ∈ 𝓝 (e.symm y) :=
        (e.isOpen_inter_preimage (isOpen_Ioo.prod isOpen_ball)).mem_nhds
          ⟨hxs, by rw [mem_preimage, hey]; exact hyV⟩
      filter_upwards [hV, hgerm _ ⟨y, hy, rfl⟩] with z hz hzF
      rw [hzF]
      have hz2 := hz.2
      simp only [mem_preimage, he z, Set.mem_prod, Set.mem_Ioo, mem_ball_zero_iff] at hz2
      obtain ⟨⟨h1, h2⟩, h3⟩ := hz2
      show heightCut l ε (θ z) *
        lateralCut R (‖(fderiv ℝ θ p).ker.orthogonalProjectionOnto (z - p)‖ ^ 2) = 1
      have hR2 : (0 : ℝ) ≤ R / 2 := by linarith
      have hmm := mul_le_mul h3.le h3.le (norm_nonneg _) hR2
      have hq : ‖(fderiv ℝ θ p).ker.orthogonalProjectionOnto (z - p)‖ ^ 2 ≤ R ^ 2 / 4 := by
        nlinarith
      rw [heightCut_eq_one hε h1.le h2.le, lateralCut_eq_one hR hq, mul_one]
    · left
      exact hzero x hxK

/-- R7 (arithmetic): the known-side cross lower bound on either arm. -/
theorem known_cross_gap_arith {c l ε R s1 s2 n1 n2 m2 : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hR : 0 < R) (h2l : 2 * l ≤ c * R ^ 2 / 18) (hs1 : -l ≤ s1) (hn2 : m2 ≤ n2) (hm2 : 0 ≤ m2)
    (hcase : l + ε / 2 ≤ s2 ∨ (-l + ε ≤ s2 ∧ R / 3 ≤ m2)) :
    min (ε / 2) (c * R ^ 2 / 18) ≤ s1 + s2 + c * (n1 ^ 2 + n2 ^ 2) := by
  have hpos : 0 ≤ c * (n1 ^ 2 + n2 ^ 2) := mul_nonneg hc.le (by positivity)
  rcases hcase with h | ⟨h, hm⟩
  · exact (min_le_left _ _).trans (by linarith)
  · have hn : R / 3 ≤ n2 := hm.trans hn2
    have hsq : R / 3 * (R / 3) ≤ n2 * n2 := mul_le_mul hn hn (by linarith) (by linarith)
    have h1 : c * (R / 3 * (R / 3)) ≤ c * (n2 * n2) := mul_le_mul_of_nonneg_left hsq hc.le
    have h2 : 0 ≤ c * n1 ^ 2 := mul_nonneg hc.le (sq_nonneg _)
    have e1 : c * (n1 ^ 2 + n2 ^ 2) = c * n1 ^ 2 + c * (n2 * n2) := by ring
    have e2 : c * (R / 3 * (R / 3)) = 2 * (c * R ^ 2 / 18) := by ring
    exact (min_le_right _ _).trans (by linarith)

/-- R7 (native): on lifted `closed D₁ × closed (S_top₂ ∪ S_lat₂)`, a source gap inequality
`θ₁x + θ₂y + c(‖x−p₁‖² + ‖y−p₂‖²) ≤ ρ̃` gives `ρ̃ ≥ dSide = min(ε/2, cR²/18)`. -/
theorem known_cross_gap {K : Type*} [NormedAddCommGroup K]
    (e1 e2 : OpenPartialHomeomorph R3 (ℝ × K)) {θ1 θ2 : R3 → ℝ} {P1 P2 : R3 → K} {p1 p2 : R3}
    (he1 : ∀ x, e1 x = (θ1 x, P1 (x - p1))) (he2 : ∀ x, e2 x = (θ2 x, P2 (x - p2)))
    (hP2 : ∀ v, ‖P2 v‖ ≤ ‖v‖) {c l ε R : ℝ} (hc : 0 < c) (hε : 0 < ε) (hR : 0 < R)
    (h2l : 2 * l ≤ c * R ^ 2 / 18) (hD1t : closedD l ε R ⊆ e1.target)
    (hS2t : closedStop l ε R ∪ closedSlat l ε R ⊆ e2.target) {x y : R3}
    (hx : x ∈ e1.symm '' closedD l ε R)
    (hy : y ∈ e2.symm '' (closedStop l ε R ∪ closedSlat l ε R)) {ρT : ℝ}
    (hgap : θ1 x + θ2 y + c * (‖x - p1‖ ^ 2 + ‖y - p2‖ ^ 2) ≤ ρT) :
    min (ε / 2) (c * R ^ 2 / 18) ≤ ρT := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  have hu1 : e1 (e1.symm u) = u := e1.right_inv (hD1t hu)
  have hw1 : e2 (e2.symm w) = w := e2.right_inv (hS2t hw)
  rw [he1] at hu1
  rw [he2] at hw1
  have hθ1 : θ1 (e1.symm u) = u.1 := congrArg Prod.fst hu1
  have hθ2 : θ2 (e2.symm w) = w.1 := congrArg Prod.fst hw1
  have hP : P2 (e2.symm w - p2) = w.2 := congrArg Prod.snd hw1
  have hn2 : ‖w.2‖ ≤ ‖e2.symm w - p2‖ := by
    rw [← hP]
    exact hP2 _
  have hu' : u ∈ Icc (-l) (l + 4 * ε) ×ˢ closedBall (0 : K) R := hu
  have hcase : l + ε / 2 ≤ w.1 ∨ (-l + ε ≤ w.1 ∧ R / 3 ≤ ‖w.2‖) := by
    rcases hw with hw | hw
    · have h' : w ∈ Icc (l + ε / 2) (l + 7 * ε / 2) ×ˢ closedBall (0 : K) (7 * R / 8) := hw
      exact Or.inl h'.1.1
    · have h' : w ∈ Icc (-l + ε) (l + 7 * ε / 2) ×ˢ
          {z : K | R / 3 ≤ ‖z‖ ∧ ‖z‖ ≤ 7 * R / 8} := hw
      exact Or.inr ⟨h'.1.1, h'.2.1⟩
  have key := known_cross_gap_arith (n1 := ‖e1.symm u - p1‖) hc hε hR h2l hu'.1.1 hn2
    (norm_nonneg _) hcase
  rw [hθ1, hθ2] at hgap
  linarith

end OAI.AnisotropicCalderon.PhaseCoordinates

end
end
