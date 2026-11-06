import C3Geometry
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask.NativeCenteredCover
open OAI.AnisotropicCalderon.MixedKernelConstructionTask.Geometry EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
  ExteriorSource ConnectionError MetricOperator MetricVolume
  ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
  CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
attribute [local instance] Classical.propDecidable

theorem exists_localPacket_with_exact_center_ball (S : KnownSideSourceData) (L : ℝ) (y0 : R3) :
    ∃ P : NativeNormalPacket S L, y0 ∈ P.centers ∧ P.centers = ball P.y0 P.rho := by
  obtain ⟨Φ, B, ε, C, ρ, H, a, w, hData⟩ :=
    exists_compact_parameter_conformalReference_framed_drift S.g1 S.g1_admissible L y0
  have hJ : JointConformalReferenceFramedDriftData S.g1 L y0 Φ B ε C ρ H a w := hData
  obtain ⟨hPos, -⟩ := hData
  obtain ⟨hNormal, hρ, hρε, -⟩ := hPos
  obtain ⟨-, hε, -, -, -, -, hroom, -⟩ := hNormal
  refine ⟨{
      y0 := y0
      Phi := Φ
      B := B
      epsGeo := ε
      Cgeo := C
      rho := ρ
      H := H
      a := a
      w := w
      native_data := hJ
      centers := ball y0 ρ
      centers_open := isOpen_ball
      centers_room := ?_
      rho_positive := hρ }, mem_ball_self hρ,rfl⟩
  intro y hy
  have hy' : ‖y - y0‖ < ρ := by rwa [mem_ball, dist_eq_norm] at hy
  refine ⟨by linarith, ?_⟩
  have h := (hroom 0 ⟨le_rfl, zero_le_one⟩ y (by linarith) 0
    (by rw [abs_zero]; linarith) 0 (mem_closedBall_self (by norm_num))).1
  simpa only [zero_smul] using h

theorem exists_nativeNormalCover_with_exact_center_balls (S : KnownSideSourceData) (L : ℝ) :
    ∃ C : NativeNormalCover S L, ∀ i, (C.packet i).centers = ball (C.packet i).y0 (C.packet i).rho := by
  choose P hP using fun y : R3 => exists_localPacket_with_exact_center_ball S L y
  obtain ⟨t, ht⟩ := isCompact_cylinder.elim_finite_subcover (fun y : R3 => (P y).centers)
    (fun y => (P y).centers_open) (fun y _ => mem_iUnion.2 ⟨y, (hP y).1⟩)
  have h0cyl : (0 : R3) ∈ cylinder := by
    refine ⟨?_, ?_, ?_⟩ <;> simp
  have hcard : 0 < t.card := by
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.1 (ht h0cyl)
    exact Finset.card_pos.2 ⟨i, hi⟩
  let pk : Fin t.card → NativeNormalPacket S L := fun k => P (t.equivFin.symm k : R3)
  choose δ hδ hinj using fun k => packet_exists_injective_radius S L (pk k)
  choose M hM hbd using fun k => packet_endpoint_bounded S L (pk k)
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.1 S.coordinateRoom_open 0 S.origin_mem
  obtain ⟨m1, hm1, hm1le⟩ := exists_pos_le_finite (fun k => min (δ k) (2 * (pk k).rho))
    (fun k => lt_min (hδ k) (by linarith [(pk k).rho_positive]))
  obtain ⟨m2, hm2, hm2le⟩ := exists_pos_le_finite (fun k => a / (M k + 1))
    (fun k => div_pos ha (by linarith [hM k]))
  have hm1δ : ∀ k, m1 ≤ δ k := fun k => (hm1le k).trans (min_le_left _ _)
  have hm1ρ : ∀ k, m1 ≤ 2 * (pk k).rho := fun k => (hm1le k).trans (min_le_right _ _)
  have hcen : ∀ k, ∀ y ∈ (pk k).centers, ‖y - (pk k).y0‖ ≤ 4 * (pk k).rho := fun k y hy =>
    ((pk k).centers_room y hy).1.le
  have hrad : ∀ k, ∀ r : ℝ, 0 < r → r < m1 → |r| ≤ 4 * (pk k).rho := fun k r hr hrm => by
    rw [abs_of_pos hr]; linarith [hm1ρ k, (pk k).rho_positive]
  have hq : ∀ lam ∈ Icc (0 : ℝ) (min m2 1), lam ∈ Icc (0 : ℝ) 1 := fun lam hl =>
    ⟨hl.1, hl.2.trans (min_le_right _ _)⟩
  refine ⟨{
      count := t.card
      count_positive := hcard
      packet := pk
      covers_cylinder := ?_
      radiusCeiling := m1
      dilationCeiling := min m2 1
      radius_positive := hm1
      dilation_positive := lt_min hm2 one_pos
      dilation_le_one := min_le_right _ _
      radius_room := fun k => by linarith [hm1ρ k, (pk k).rho_positive]
      normal_injective := ?_
      coordinate_room := ?_
      endpoint_coherence := ?_ },?_⟩
  · intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (ht hy)
    refine ⟨t.equivFin ⟨i, hi⟩, ?_⟩
    show y ∈ (P (t.equivFin.symm (t.equivFin ⟨i, hi⟩) : R3)).centers
    rw [Equiv.symm_apply_apply]
    exact hyi
  · intro k lam hlam y hy r hr hrm
    exact hinj k lam (hq lam hlam) y (hcen k y hy) r hr ((le_of_lt hrm).trans (hm1δ k))
  · intro k lam hlam y hy r hr hrm z hz
    apply hball
    have hb := hbd k lam (hq lam hlam) y (hcen k y hy) r (hrad k r hr hrm) z hz
    have hlam0 : 0 ≤ lam := hlam.1
    have hlamle : lam ≤ a / (M k + 1) := hlam.2.trans ((min_le_left _ _).trans (hm2le k))
    have hMk : 0 < M k + 1 := by linarith [hM k]
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam0]
    calc lam * ‖packetEndpoint S L (pk k) lam y r z‖ ≤ a / (M k + 1) * M k :=
          mul_le_mul hlamle hb (norm_nonneg _) (div_pos ha hMk).le
      _ < a := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hMk]
          nlinarith
  · intro i j lam hlam y hy r hr hrm z hz
    exact packet_endpoint_coherence S L (pk i) (pk j) lam (hq lam hlam) y
      (hcen i y hy.1) (hcen j y hy.2) r (hrad i r hr hrm) (hrad j r hr hrm) z hz

  · intro i
    exact (hP (t.equivFin.symm i : R3)).2

theorem exists_nativeNormalCover_with_rho_center_room (S : KnownSideSourceData) (L : ℝ) :
    ∃ C : NativeNormalCover S L, ∀ i, ∀ y ∈ (C.packet i).centers,
      ‖y-(C.packet i).y0‖ < (C.packet i).rho := by
  obtain ⟨C,hC⟩ := exists_nativeNormalCover_with_exact_center_balls S L
  refine ⟨C,?_⟩
  intro i y hy
  rw [hC i,mem_ball,dist_eq_norm] at hy
  exact hy

end OAI.AnisotropicCalderon.MixedKernelConstructionTask.NativeCenteredCover
