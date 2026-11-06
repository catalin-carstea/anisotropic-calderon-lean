import MixedKernelNativeProductAndBasis
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

theorem cross_source_original_kernel_joint_regular : OriginalKernelJointRegularityGoal :=
  v021_original_kernel_joint_regular
theorem cross_source_normal_packet_cover_exists : NativeNormalPacketCoverGoal :=
  v021_normal_packet_cover_exists
theorem cross_source_initial_cross_product : InitialCrossProductGoal := v021_initial_cross_product

section NativeBasisArm
open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise

/-- NBA0: the actual native rooms are open, with the observation and inner rooms inside. -/
theorem native_room_open_subsets {θ : R3 → ℝ} {p : R3}
    (e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker)) {l ε R : ℝ}
    (hε : 0 < ε) (hl : 4 * ε < l) (hR : 0 < R)
    (hDt : PhaseCoordinates.closedD l ε R ⊆ e.target) :
    IsOpen (e.symm '' PhaseCoordinates.roomD l ε R) ∧
    e.symm '' PhaseCoordinates.roomO l ε R ⊆ e.symm '' PhaseCoordinates.roomD l ε R ∧
    e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
      e.symm '' PhaseCoordinates.roomD l ε R := by
  have hDo : IsOpen (PhaseCoordinates.roomD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) := by
    exact isOpen_Ioo.prod Metric.isOpen_ball
  refine ⟨e.isOpen_image_symm_of_subset_target hDo
      (PhaseCoordinates.roomD_subset_closedD.trans hDt),
    Set.image_mono (PhaseCoordinates.roomO_subset_closedO.trans
      (PhaseCoordinates.closedO_subset_roomD hε hl hR)), Set.image_mono fun u hu => ?_⟩
  rcases hu with hu | hu
  · exact PhaseCoordinates.closedStop_subset_roomD hε hl hR
      (PhaseCoordinates.roomStop_subset_closedStop hu)
  · exact PhaseCoordinates.closedSlat_subset_roomD hε hl hR
      (PhaseCoordinates.roomSlat_subset_closedSlat hu)

/-- The SAME dilated first coefficient is positive definite (ORIGINAL admissibility at `lam • x`). -/
theorem dilatedFirstPrincipal_posDef (S : KnownSideSourceData) (lam : ℝ) (x : R3) :
    (dilatedFirstPrincipal S lam x).PosDef :=
  principalCoefficient_posDef S.g1 S.g1_admissible (lam • x)

/-- The basis-arm conclusion `‖R_O wᵢ‖ ≤ Kint μᵢ^γ` for EVERY Hilbert basis / Gram system of the
SAME harmonic space of the literal dilated first coefficient on `D` (a name for the statement only;
it is a conclusion, never a premise of the endpoint). -/
def FirstBasisArmOn (S : KnownSideSourceData) (lam : ℝ) (D O Sv : Set R3) (Kint γ : ℝ) : Prop :=
  ∀ (hD : IsOpen D) (hOD : O ⊆ D) (hSD : Sv ⊆ D)
    (ι : Type) (w : HilbertBasis ι ℝ (harmonicSub D hD
      (dilatedFirstPrincipal S lam) (contDiff_dilatedFirstPrincipal S lam).contDiffOn))
    (μ : ι → ℝ), (∀ i, 0 < μ i) →
    (∀ i j, inner ℝ (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn Sv hSD (w i))
      (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn Sv hSD (w j)) =
        if i = j then μ i ^ 2 else 0) →
    ∀ i, ‖harmonicRestrict D hD (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn O hOD (w i)‖ ≤ Kint * μ i ^ γ

/-- NBA1 (room form): the literal first-operator room interpolation, on ANY rooms `O, Sv ⊆ D`,
gives the basis arm for every Gram system of the SAME harmonic space of `dilatedFirstPrincipal`. -/
theorem first_basis_arm_on_of_room (S : KnownSideSourceData) (lam : ℝ) (D O Sv : Set R3)
    {Kint γ : ℝ}
    (HI : ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict D)) (q : R3 → ℝ),
      q =ᵐ[(volume : Measure R3).restrict D] (u : R3 → ℝ) → ContDiffOn ℝ ∞ q D →
      (∀ x ∈ D,
        coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) q) x = 0) →
      ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict O))
        (uS : Lp ℝ 2 ((volume : Measure R3).restrict Sv)),
      q =ᵐ[(volume : Measure R3).restrict O] (uO : R3 → ℝ) →
      q =ᵐ[(volume : Measure R3).restrict Sv] (uS : R3 → ℝ) →
      ‖uO‖ ≤ Kint * (‖uS‖ ^ γ * ‖u‖ ^ (1 - γ))) :
    FirstBasisArmOn S lam D O Sv Kint γ :=
  fun hD hOD hSD ι w μ hμ hgram i =>
    harmonic_basis_interp_bound_spectral D O Sv hD (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn
      (fun x _ => dilatedFirstPrincipal_posDef S lam x) hOD hSD
      (fun u q hq hcq hP uO uS hO hS => HI u q hq hcq
        (fun x hx => (coordinateFluxDivergence_eq_divCoeffGrad _ q x).trans (hP x hx))
        uO uS hO hS)
      w μ hμ hgram i

/-- NBA1: the actual native FIRST basis arm `‖R_O wᵢ‖ ≤ Kint μᵢ^γ₁` on the SAME known-side rooms,
for every Hilbert basis / Gram system of the SAME harmonic space of the literal first operator. -/
theorem native_first_basis_arm (S : KnownSideSourceData) :
    ∃ a1 : ℝ, 0 < a1 ∧ ∀ lam : ℝ, 0 < lam → ∀ p : R3,
    lam • p ∈ Metric.ball (0 : R3) a1 → S.separating_function (lam • p) = 0 →
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧
      (∀ k, pd k θ p = pd k (fun x => -S.separating_function (lam • x)) p) ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      l < c * R ^ 2 / 9 →
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
  obtain ⟨a1, ha1, H⟩ := native_first_known_side_rooms_near S
  refine ⟨a1, ha1, fun lam hlam p hp hp0 => ?_⟩
  obtain ⟨θ, hθ, h0, hd, c, hc, e, he, κ0, hκ0, H1⟩ := H lam hlam p hp hp0
  refine ⟨θ, hθ, h0, hd, c, hc, e, he, κ0, hκ0, fun κ hκ hκ0' => ?_⟩
  obtain ⟨ρ, hρ, H2⟩ := H1 κ hκ hκ0'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 hlR => ?_⟩
  obtain ⟨hDt, hroom, hW, Kint, hKint, HI⟩ := H2 l ε R hε hl hR hlρ hRρ hκh hε4 hlR
  obtain ⟨hDo, hOD, hSD⟩ := native_room_open_subsets e hε hl hR hDt
  have hκl : κ * l ≤ 1 / 4 := by nlinarith [mul_pos hκ hε]
  obtain ⟨-, -, hg1, hg2⟩ := strictExponent_bounds hκ (by linarith) hκl hε.le hε4
  exact ⟨hDo, hOD, hSD, hroom, hW, hg1, hg2, Kint, hKint,
    first_basis_arm_on_of_room S lam _ _ _ HI⟩

/-- NBA2: the actual native SECOND coefficient arm. A literal second-operator solution on the
SAME known-side room with observed norm `≤ M` and room norm `≤ M/μ` has
`‖b‖_O ≤ Kint M μ^(γ₂-1)` (unnormalized `b`) and `μ ‖b‖_O ≤ Kint M μ^γ₂` (normalized `μ b`). -/
theorem native_second_coefficient_arm (S : KnownSideSourceData) (L : ℝ) :
    ∃ a1 : ℝ, 0 < a1 ∧ ∀ lam : ℝ, 0 < lam → ∀ p : R3,
    lam • p ∈ Metric.ball (0 : R3) a1 → S.separating_function (lam • p) = 0 →
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧
      (∀ k, pd k θ p = pd k (fun x => -S.separating_function (lam • x)) p) ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
    ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R →
      l + 4 * ε ≤ ρ → R ≤ ρ → κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 →
      l < c * R ^ 2 / 9 →
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
  obtain ⟨a1, ha1, H⟩ := native_second_known_side_rooms_near S L
  refine ⟨a1, ha1, fun lam hlam p hp hp0 => ?_⟩
  obtain ⟨θ, hθ, h0, hd, c, hc, e, he, κ0, hκ0, H1⟩ := H lam hlam p hp hp0
  refine ⟨θ, hθ, h0, hd, c, hc, e, he, κ0, hκ0, fun κ hκ hκ0' => ?_⟩
  obtain ⟨ρ, hρ, H2⟩ := H1 κ hκ hκ0'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 hlR => ?_⟩
  obtain ⟨hDt, hroom, hW, Kint, hKint, HI⟩ := H2 l ε R hε hl hR hlρ hRρ hκh hε4 hlR
  obtain ⟨hDo, hOD, hSD⟩ := native_room_open_subsets e hε hl hR hDt
  have hκl : κ * l ≤ 1 / 4 := by nlinarith [mul_pos hκ hε]
  obtain ⟨-, -, hg1, hg2⟩ := strictExponent_bounds hκ (by linarith) hκl hε.le hε4
  refine ⟨hDo, hOD, hSD, hroom, hW, hg1, hg2, Kint, hKint,
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

end NativeBasisArm

section CoefficientBound
open MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- CB1: Cauchy–Schwarz for two real L² functions on one measure. -/
theorem abs_integral_mul_le_sqrt {m : Measure R3} {f g : R3 → ℝ} (hf : MemLp f 2 m)
    (hg : MemLp g 2 m) :
    |∫ x, f x * g x ∂m| ≤ Real.sqrt (∫ x, f x ^ 2 ∂m) * Real.sqrt (∫ x, g x ^ 2 ∂m) := by
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := m) Real.HolderConjugate.two_two
    (f := fun x => ‖f x‖) (g := fun x => ‖g x‖)
    (ae_of_all _ fun x => norm_nonneg _) (ae_of_all _ fun x => norm_nonneg _)
    (by rw [h2]; exact hf.norm) (by rw [h2]; exact hg.norm)
  have e : ∀ h : R3 → ℝ, (fun x => ‖h x‖ ^ (2 : ℝ)) = fun x => h x ^ 2 := fun h =>
    funext fun x => by rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [e f, e g, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hH
  calc |∫ x, f x * g x ∂m| = ‖∫ x, f x * g x ∂m‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, ‖f x * g x‖ ∂m := norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ * ‖g x‖ ∂m := by simp_rw [norm_mul]
    _ ≤ _ := hH

/-- CB2: the normalized coefficient `(μ²)⁻¹ ∫ f q` with `∫ q² = μ²` is bounded by `(μ²)⁻¹ ∫ f²`. -/
theorem coefficient_sq_le {m : Measure R3} {f q : R3 → ℝ} (hf : MemLp f 2 m) (hq : MemLp q 2 m)
    {μ : ℝ} (hμ : 0 < μ) (hqμ : ∫ x, q x ^ 2 ∂m = μ ^ 2) :
    ((μ ^ 2)⁻¹ * ∫ x, f x * q x ∂m) ^ 2 ≤ (μ ^ 2)⁻¹ * ∫ x, f x ^ 2 ∂m := by
  have hA : 0 ≤ ∫ x, f x ^ 2 ∂m := integral_nonneg fun x => sq_nonneg _
  have hI := abs_integral_mul_le_sqrt hf hq
  rw [hqμ, Real.sqrt_sq hμ.le] at hI
  have hμ2 : 0 < μ ^ 2 := by positivity
  have h3 : (∫ x, f x * q x ∂m) ^ 2 ≤ (∫ x, f x ^ 2 ∂m) * μ ^ 2 := by
    have h4 : (∫ x, f x * q x ∂m) ^ 2 ≤ (Real.sqrt (∫ x, f x ^ 2 ∂m) * μ) ^ 2 := by
      rw [← sq_abs (∫ x, f x * q x ∂m)]
      exact pow_le_pow_left₀ (abs_nonneg _) hI 2
    rwa [mul_pow, Real.sq_sqrt hA] at h4
  have key : (μ ^ 2)⁻¹ * (∫ x, f x * q x ∂m) ^ 2 ≤ ∫ x, f x ^ 2 ∂m := by
    rw [inv_mul_le_iff₀ hμ2]
    nlinarith [h3]
  calc ((μ ^ 2)⁻¹ * ∫ x, f x * q x ∂m) ^ 2 =
        (μ ^ 2)⁻¹ * ((μ ^ 2)⁻¹ * (∫ x, f x * q x ∂m) ^ 2) := by ring
    _ ≤ (μ ^ 2)⁻¹ * ∫ x, f x ^ 2 ∂m := mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hμ2.le)

/-- CB3: a pointwise square bound on a finite-measure room bounds the SAME L² class. -/
theorem lp_norm_sq_le_of_sq_le {V : Set R3} (hV : MeasurableSet V)
    (hVfin : (volume : Measure R3) V < ⊤) {b : R3 → ℝ}
    (bD : Lp ℝ 2 ((volume : Measure R3).restrict V))
    (hb : b =ᵐ[(volume : Measure R3).restrict V] (bD : R3 → ℝ)) {C : ℝ}
    (hpt : ∀ y ∈ V, b y ^ 2 ≤ C) :
    ‖bD‖ ^ 2 ≤ C * ((volume : Measure R3) V).toReal := by
  have : IsFiniteMeasure ((volume : Measure R3).restrict V) :=
    isFiniteMeasure_restrict.mpr hVfin.ne
  have hint : Integrable (fun y => (bD : R3 → ℝ) y ^ 2) ((volume : Measure R3).restrict V) :=
    (Lp.memLp bD).integrable_sq
  rw [← integral_sq_eq_norm_sq bD]
  have hle : ∫ y, (bD : R3 → ℝ) y ^ 2 ∂((volume : Measure R3).restrict V) ≤
      ∫ _y, C ∂((volume : Measure R3).restrict V) := by
    refine integral_mono_ae hint (integrable_const C) ?_
    filter_upwards [ae_restrict_mem hV, hb] with y hy hby
    rw [← hby]
    exact hpt y hy
  rw [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ] at hle
  linarith [mul_comm C ((volume : Measure R3) V).toReal]

/-- CB4: the ACTUAL extended coefficient of (cross:coefficient-extension) on the SAME product
room satisfies `‖b‖_{L²(V)} ≤ M/μ`, with `M` chosen before `μ`, `q` and any spectral system. -/
theorem initialCoefficient_room_bound (S : KnownSideSourceData) (lam : ℝ) (hlam : 0 < lam)
    (U V K J : Set R3) (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hJ : IsCompact J) (hUK : U ⊆ K) (hVJ : V ⊆ J)
    (hcross : K ×ˢ J ⊆ initialCross S lam) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ μ : ℝ, 0 < μ → ∀ q : R3 → ℝ, MemLp q 2 ((volume : Measure R3).restrict U) →
      ∫ x, q x ^ 2 ∂((volume : Measure R3).restrict U) = μ ^ 2 →
      ∀ bD : Lp ℝ 2 ((volume : Measure R3).restrict V),
      initialCoefficient S lam U μ q =ᵐ[(volume : Measure R3).restrict V] (bD : R3 → ℝ) →
      ‖bD‖ ≤ M / μ := by
  have hF := Geometry.initialKernel_contDiffOn S lam hlam
  obtain ⟨C0, hC0⟩ := (hK.prod hJ).exists_bound_of_continuousOn (hF.continuousOn.mono hcross)
  have hC1 : 0 ≤ max C0 0 := le_max_right _ _
  have hb1 : ∀ v ∈ K ×ˢ J, |initialKernel S lam v| ≤ max C0 0 := by
    intro v hv
    have h := hC0 v hv
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  have hUfin : (volume : Measure R3) U < ⊤ := (measure_mono hUK).trans_lt hK.measure_lt_top
  have hVfin : (volume : Measure R3) V < ⊤ := (measure_mono hVJ).trans_lt hJ.measure_lt_top
  have : IsFiniteMeasure ((volume : Measure R3).restrict U) :=
    isFiniteMeasure_restrict.mpr hUfin.ne
  have hab : 0 ≤ ((volume : Measure R3) U).toReal * ((volume : Measure R3) V).toReal :=
    mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  refine ⟨max C0 0 * Real.sqrt (((volume : Measure R3) U).toReal *
      ((volume : Measure R3) V).toReal), mul_nonneg hC1 (Real.sqrt_nonneg _),
    fun μ hμ q hq hqμ bD hbD => ?_⟩
  have hslice : ∀ y ∈ V,
      MemLp (fun x => initialKernel S lam (x, y)) 2 ((volume : Measure R3).restrict U) ∧
      ∫ x, initialKernel S lam (x, y) ^ 2 ∂((volume : Measure R3).restrict U) ≤
        ((volume : Measure R3) U).toReal * max C0 0 ^ 2 := by
    intro y hy
    have hcont : ContinuousOn (fun x => initialKernel S lam (x, y)) U :=
      (hF.continuousOn.mono hcross).comp (continuousOn_id.prodMk continuousOn_const)
        (fun x hx => ⟨hUK hx, hVJ hy⟩)
    have hbd : ∀ᵐ x ∂((volume : Measure R3).restrict U),
        ‖initialKernel S lam (x, y)‖ ≤ max C0 0 := by
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      rw [Real.norm_eq_abs]
      exact hb1 _ ⟨hUK hx, hVJ hy⟩
    have hmem : MemLp (fun x => initialKernel S lam (x, y)) 2 ((volume : Measure R3).restrict U) :=
      MemLp.of_bound (hcont.aestronglyMeasurable hU.measurableSet) (max C0 0) hbd
    refine ⟨hmem, ?_⟩
    have hle : ∫ x, initialKernel S lam (x, y) ^ 2 ∂((volume : Measure R3).restrict U) ≤
        ∫ _x, max C0 0 ^ 2 ∂((volume : Measure R3).restrict U) := by
      refine integral_mono_ae hmem.integrable_sq (integrable_const _) ?_
      filter_upwards [hbd] with x hx
      rw [Real.norm_eq_abs] at hx
      exact sq_le_sq' (neg_le_of_abs_le hx) (le_of_abs_le hx)
    rwa [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ] at hle
  have hpt : ∀ y ∈ V, initialCoefficient S lam U μ q y ^ 2 ≤
      (μ ^ 2)⁻¹ * (((volume : Measure R3) U).toReal * max C0 0 ^ 2) := by
    intro y hy
    obtain ⟨hmem, hint⟩ := hslice y hy
    have h := coefficient_sq_le hmem hq hμ hqμ
    calc initialCoefficient S lam U μ q y ^ 2 =
          ((μ ^ 2)⁻¹ * ∫ x, initialKernel S lam (x, y) * q x
            ∂((volume : Measure R3).restrict U)) ^ 2 := rfl
      _ ≤ (μ ^ 2)⁻¹ * ∫ x, initialKernel S lam (x, y) ^ 2
            ∂((volume : Measure R3).restrict U) := h
      _ ≤ (μ ^ 2)⁻¹ * (((volume : Measure R3) U).toReal * max C0 0 ^ 2) :=
          mul_le_mul_of_nonneg_left hint (by positivity)
  have h := lp_norm_sq_le_of_sq_le hV.measurableSet hVfin bD hbD hpt
  have hR : (max C0 0 * Real.sqrt (((volume : Measure R3) U).toReal *
      ((volume : Measure R3) V).toReal) / μ) ^ 2 =
      (μ ^ 2)⁻¹ * (((volume : Measure R3) U).toReal * max C0 0 ^ 2) *
        ((volume : Measure R3) V).toReal := by
    rw [div_pow, mul_pow, Real.sq_sqrt hab, div_eq_inv_mul]
    ring
  calc ‖bD‖ = Real.sqrt (‖bD‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((max C0 0 * Real.sqrt (((volume : Measure R3) U).toReal *
          ((volume : Measure R3) V).toReal) / μ) ^ 2) := Real.sqrt_le_sqrt (by rw [hR]; exact h)
    _ = _ := Real.sqrt_sq (div_nonneg (mul_nonneg hC1 (Real.sqrt_nonneg _)) hμ.le)

/-- CB5: CB4 on the SAME restricted singular vectors `R wᵢ` and SAME singular values of the
actual first harmonic space: `‖bᵢ‖_{L²(V)} ≤ M/μᵢ`, ONE `M` before the spectral system. -/
theorem actualCoefficient_room_bound (S : KnownSideSourceData) (lam : ℝ) (hlam : 0 < lam)
    (D : Set R3) (hD : IsOpen D) (U V K J : Set R3) (hU : IsOpen U) (hV : IsOpen V)
    (hK : IsCompact K) (hJ : IsCompact J) (hUK : U ⊆ K) (hVJ : V ⊆ J) (hUD : U ⊆ D)
    (hcross : K ×ˢ J ⊆ initialCross S lam) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ι : Type)
      (w : ι → harmonicSub D hD (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn) (μ : ι → ℝ), (∀ i, 0 < μ i) →
      (∀ i j, inner ℝ (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn U hUD (w i))
        (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn U hUD (w j)) =
          if i = j then μ i ^ 2 else 0) →
      ∀ (i : ι) (bD : Lp ℝ 2 ((volume : Measure R3).restrict V)),
      initialCoefficient S lam U (μ i) (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn U hUD (w i))
        =ᵐ[(volume : Measure R3).restrict V] (bD : R3 → ℝ) →
      ‖bD‖ ≤ M / μ i := by
  obtain ⟨M, hM, H⟩ := initialCoefficient_room_bound S lam hlam U V K J hU hV hK hJ hUK hVJ hcross
  refine ⟨M, hM, fun ι w μ hμ hgram i bD hb => H (μ i) (hμ i) _ (Lp.memLp _) ?_ bD hb⟩
  rw [integral_sq_eq_norm_sq, ← real_inner_self_eq_norm_sq, hgram, if_pos rfl]

/-- CS1: the two strict exponents (each `> 1/2`, from `strictExponent_bounds` as exported by
NBA1/NBA2) give `γ₁+γ₂-1 > 0`; with all-power summability of the SAME singular values, the
tensor summands `fᵢ ⊗ gᵢ` (`‖fᵢ‖ ≤ Cμᵢ^γ₁`, `‖gᵢ‖ ≤ C'μᵢ^(γ₂-1)`, unnormalized `b`) are summable. -/
theorem cross_tensor_summable_of_strict {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {n : Measure β} [SFinite m] [SFinite n] {ι : Type*}
    (f : ι → Lp ℝ 2 m) (g : ι → Lp ℝ 2 n) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    {C C' γ₁ γ₂ : ℝ} (hC : 0 ≤ C)
    (hf : ∀ i, ‖f i‖ ≤ C * μ i ^ γ₁) (hg : ∀ i, ‖g i‖ ≤ C' * μ i ^ (γ₂ - 1))
    (hγ₁ : 1 / 2 < γ₁) (hγ₂ : 1 / 2 < γ₂)
    (hsum : ∀ b : ℝ, 0 < b → Summable fun i => μ i ^ b) :
    0 < γ₁ + γ₂ - 1 ∧ Summable fun i => tensorLp (f i) (g i) :=
  ⟨by linarith, tensor_summable_of_rpow_bounds f g μ hμ C C' γ₁ γ₂ hC hf hg
    (hsum _ (by linarith))⟩

/-- AD1: the eigen relation `R*R w = μ² w` of the SAME singular system turns restricted inner
products into full ones: `⟪R u, R w⟫ = μ² ⟪u, w⟫`. -/
theorem inner_restrict_eq_of_eigen {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (R : E →L[ℝ] F) (u w : E) (μ : ℝ)
    (h : (ContinuousLinearMap.adjoint R ∘L R) w = μ ^ 2 • w) :
    inner ℝ (R u) (R w) = μ ^ 2 * inner ℝ u w := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply, h,
    real_inner_smul_right]

end CoefficientBound

section ObservedCoefficient
open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise

/-- OB: the observed-side bound `‖bᵢ‖_{L²(V)} ≤ M` for the ACTUAL coefficient
`bᵢ = initialCoefficient S lam T μᵢ (R_T wᵢ)`, through the supplied full/restricted agreement and the
μ-independent full-domain Fubini bound; `M = ‖F‖_{L²(D×V)}` is chosen before the spectral system. -/
theorem actualCoefficient_observed_bound (S : KnownSideSourceData) (lam : ℝ) (hlam : 0 < lam)
    (D K T V J : Set R3) (hD : IsOpen D) (hK : IsCompact K) (hDK : D ⊆ K) (hTD : T ⊆ D)
    (hV : IsOpen V) (hJ : IsCompact J) (hVJ : V ⊆ J) (hcross : K ×ˢ J ⊆ initialCross S lam) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ι : Type)
      (w : HilbertBasis ι ℝ (harmonicSub D hD (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ), (∀ i, 0 < μ i) →
      (∀ i, (ContinuousLinearMap.adjoint (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD) ∘L
        harmonicRestrict D hD (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD) (w i) = μ i ^ 2 • w i) →
      ∀ i : ι, ∃ hb : MemLp (initialCoefficient S lam T (μ i)
          (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
            (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD (w i)))
          2 ((volume : Measure R3).restrict V),
        ‖hb.toLp (initialCoefficient S lam T (μ i)
          (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
            (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD (w i)))‖ ≤ M := by
  have hF := initialKernel_memLp_product S lam hlam D V K J hD hV hK hJ hDK hVJ hcross
  refine ⟨‖hF.toLp (initialKernel S lam)‖, norm_nonneg _, fun ι w μ hμ heigen i => ?_⟩
  obtain ⟨hb1, hbound⟩ := harmonicIntegralCoefficient_memLp_and_norm_le
    ((volume : Measure R3).restrict D) ((volume : Measure R3).restrict V) _ w
    (initialKernel S lam) hF i
  have hagree := initialKernel_integralCoefficient_agreement S lam hlam D K T V hD hK hDK hTD
    (fun y hy x hx => hcross ⟨hx, hVJ hy⟩) w μ hμ heigen i
  have hae : initialCoefficient S lam T (μ i)
      (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD (w i))
      =ᵐ[(volume : Measure R3).restrict V]
      integralCoefficient ((volume : Measure R3).restrict D) (initialKernel S lam)
        (w i : Lp ℝ 2 ((volume : Measure R3).restrict D)) 1 :=
    (ae_restrict_mem hV.measurableSet).mono fun y hy => hagree hy
  have hb : MemLp (initialCoefficient S lam T (μ i)
      (harmonicRestrict D hD (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD (w i)))
      2 ((volume : Measure R3).restrict V) := MemLp.ae_eq hae.symm hb1
  refine ⟨hb, ?_⟩
  rw [(MemLp.toLp_eq_toLp_iff hb hb1).mpr hae]
  exact hbound

/-- The actual coefficient IS the supplied integral coefficient on the SAME room (definitional). -/
theorem initialCoefficient_eq_integralCoefficient (S : KnownSideSourceData) (lam : ℝ)
    (U : Set R3) (μi : ℝ) (q : R3 → ℝ) :
    initialCoefficient S lam U μi q =
      integralCoefficient ((volume : Measure R3).restrict U) (initialKernel S lam) q (μi ^ 2)⁻¹ :=
  rfl

/-- SF-a: the room arm `‖bᵢ‖_{L²(D2)} ≤ M/μᵢ` WITH the actual L² class, from the supplied
generic Fubini bound and `‖R wᵢ‖ = μᵢ` (Gram); `M = ‖F‖_{L²(T×D2)}` before the spectral system. -/
theorem actualCoefficient_room_memLp (S : KnownSideSourceData) (lam : ℝ) (hlam : 0 < lam)
    (D1 : Set R3) (hD1 : IsOpen D1) (T KT D2 J2 : Set R3) (hT : IsOpen T) (hKT : IsCompact KT)
    (hTKT : T ⊆ KT) (hTD1 : T ⊆ D1) (hD2 : IsOpen D2) (hJ2 : IsCompact J2) (hD2J2 : D2 ⊆ J2)
    (hrow : KT ×ˢ J2 ⊆ initialCross S lam) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ι : Type)
      (w : ι → harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn) (μ : ι → ℝ), (∀ i, 0 < μ i) →
      (∀ i j, inner ℝ (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w i))
        (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w j)) =
          if i = j then μ i ^ 2 else 0) →
      ∀ i : ι, ∃ hb : MemLp (initialCoefficient S lam T (μ i)
          (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
            (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w i)))
          2 ((volume : Measure R3).restrict D2),
        ‖hb.toLp (initialCoefficient S lam T (μ i)
          (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
            (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w i)))‖ ≤ M / μ i := by
  have hF := initialKernel_memLp_product S lam hlam T D2 KT J2 hT hD2 hKT hJ2 hTKT hD2J2 hrow
  refine ⟨‖hF.toLp (initialKernel S lam)‖, norm_nonneg _, ?_⟩
  intro ι w μ hμ hgram i
  have hn : ‖harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w i)‖ = μ i := by
    have h := hgram i i
    rw [if_pos rfl, real_inner_self_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (hμ i).le).mp h
  obtain ⟨hb, hbd⟩ := integralCoefficient_memLp_and_norm_le
    ((volume : Measure R3).restrict T) ((volume : Measure R3).restrict D2)
    (initialKernel S lam) hF (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w i)) (μ i ^ 2)⁻¹
  rw [initialCoefficient_eq_integralCoefficient]
  refine ⟨hb, hbd.trans_eq ?_⟩
  rw [hn, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)), pow_two, mul_inv,
    mul_assoc (μ i)⁻¹ (μ i)⁻¹ (μ i), inv_mul_cancel₀ (hμ i).ne', mul_one, div_eq_inv_mul]

/-- Name of the SF conclusion (a statement only, never an endpoint premise): `b` is smooth and
solves the literal second PDE on `D2`, is L² on `D2` with norm `≤ M/μ` and on `S2` with norm `≤ M`. -/
def SecondCoefficientArmsOn (S : KnownSideSourceData) (L lam : ℝ) (D2 S2 : Set R3) (M μi : ℝ)
    (b : R3 → ℝ) : Prop :=
  ContDiffOn ℝ ∞ b D2 ∧ (∀ y ∈ D2, normalizedSecondLaplacian S.g1 S.g2 L lam b y = 0) ∧
  (∃ hb : MemLp b 2 ((volume : Measure R3).restrict D2), ‖hb.toLp b‖ ≤ M / μi) ∧
  (∃ hb : MemLp b 2 ((volume : Measure R3).restrict S2), ‖hb.toLp b‖ ≤ M)

/-- Name (statement only) of the SAME actual singular system of `R_T` on the first harmonic space:
positive `μ`, the eigen relation `R_T* R_T wᵢ = μᵢ² wᵢ`, and the Gram relation. -/
def ActualSingularSystem (S : KnownSideSourceData) (lam : ℝ) (D1 : Set R3) (hD1 : IsOpen D1)
    (T : Set R3) (hTD1 : T ⊆ D1) (ι : Type)
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ) : Prop :=
  (∀ i, 0 < μ i) ∧
  (∀ i, (ContinuousLinearMap.adjoint (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1) ∘L
    harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1) (w i) = μ i ^ 2 • w i) ∧
  (∀ i j, inner ℝ (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w i))
    (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w j)) =
      if i = j then μ i ^ 2 else 0)

/-- SF: BOTH coefficient bounds of Lemma cross:series on the SAME singular family: the actual
`bᵢ` is smooth and solves the literal second PDE on `D2`, `‖bᵢ‖_{D2} ≤ M/μᵢ`, `‖bᵢ‖_{S2} ≤ M`,
with ONE `M` chosen before `(ι, w, μ)`. -/
theorem actualCoefficient_both_bounds (S : KnownSideSourceData) (L lam : ℝ) (hlam : 0 < lam)
    (D1 K1 T KT D2 J2 S2 JS : Set R3) (hD1 : IsOpen D1) (hK1 : IsCompact K1) (hD1K1 : D1 ⊆ K1)
    (hT : IsOpen T) (hKT : IsCompact KT) (hTKT : T ⊆ KT) (hTD1 : T ⊆ D1)
    (hD2 : IsOpen D2) (hJ2 : IsCompact J2) (hD2J2 : D2 ⊆ J2)
    (hS2 : IsOpen S2) (hJS : IsCompact JS) (hS2JS : S2 ⊆ JS)
    (hrow : KT ×ˢ J2 ⊆ initialCross S lam) (hobs : K1 ×ˢ JS ⊆ initialCross S lam) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ι : Type)
      (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ),
      ActualSingularSystem S lam D1 hD1 T hTD1 ι w μ →
      ∀ i : ι, SecondCoefficientArmsOn S L lam D2 S2 M (μ i)
        (initialCoefficient S lam T (μ i) (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w i))) := by
  obtain ⟨M2, hM2, HO⟩ := actualCoefficient_observed_bound S lam hlam D1 K1 T S2 JS hD1 hK1
    hD1K1 hTD1 hS2 hJS hS2JS hobs
  obtain ⟨M1, hM1, HR⟩ := actualCoefficient_room_memLp S lam hlam D1 hD1 T KT D2 J2 hT hKT hTKT
    hTD1 hD2 hJ2 hD2J2 hrow
  refine ⟨max M1 M2, le_max_of_le_right hM2, ?_⟩
  rintro ι w μ ⟨hμ, heigen, hgram⟩ i
  have hPDE := initialCoefficient_secondPDE S L lam hlam T D2 KT J2 hT hD2 hKT hJ2 hTKT hD2J2
    hrow (μ i) _ (Lp.memLp (harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn T hTD1 (w i)))
  obtain ⟨hb, hbd⟩ := HR ι w μ hμ hgram i
  obtain ⟨hs, hsd⟩ := HO ι w μ hμ heigen i
  unfold SecondCoefficientArmsOn
  refine ⟨hPDE.1, hPDE.2, ⟨hb, hbd.trans ?_⟩, ⟨hs, hsd.trans (le_max_right _ _)⟩⟩
  exact div_le_div_of_nonneg_right (le_max_left _ _) (hμ i).le

end ObservedCoefficient

section CompactCollar

/-- CC1: the CLOSED top/lateral collar lies in the union of three PERTURBED open collars. -/
theorem closedCollar_subset_perturbed {K : Type*} [NormedAddCommGroup K] {l ε R : ℝ}
    (hε : 0 < ε) (hR : 0 < R) :
    PhaseCoordinates.closedStop (K := K) l ε R ∪ PhaseCoordinates.closedSlat l ε R ⊆
      (PhaseCoordinates.roomStop (l - ε / 8) (9 * ε / 8) (5 * R / 4) ∪
          PhaseCoordinates.roomSlat (l - ε / 8) (9 * ε / 8) (5 * R / 4)) ∪
        (PhaseCoordinates.roomStop (l + ε / 8) ε (3 * R / 4) ∪
          PhaseCoordinates.roomSlat (l + ε / 8) ε (3 * R / 4)) ∪
        (PhaseCoordinates.roomStop (l + ε / 8) ε (5 * R / 4) ∪
          PhaseCoordinates.roomSlat (l + ε / 8) ε (5 * R / 4)) := by
  rintro ⟨t, z⟩ hu
  simp only [PhaseCoordinates.closedStop, PhaseCoordinates.closedSlat,
    PhaseCoordinates.roomStop, PhaseCoordinates.roomSlat, Set.mem_union, Set.mem_prod,
    Set.mem_Icc, Set.mem_Ioo, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right,
    Set.mem_setOf_eq] at hu ⊢
  rcases hu with ⟨⟨ht1, ht2⟩, hz⟩ | ⟨⟨ht1, ht2⟩, hz1, hz2⟩
  · exact Or.inl (Or.inl (Or.inl ⟨⟨by linarith, by linarith⟩, by linarith⟩))
  · by_cases h : ‖z‖ < 21 * R / 32
    · exact Or.inl (Or.inr (Or.inr ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩))
    · push_neg at h
      exact Or.inr (Or.inr ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩)

/-- CC2: if every ADMISSIBLE open collar of the SAME chart maps into a set, so does the CLOSED
collar of any slack-admissible triple (the three perturbed triples of CC1 are admissible). -/
theorem closedCollar_mem_of_open_collars {K : Type*} [NormedAddCommGroup K] (f : ℝ × K → R3)
    (P : R3 → Prop) {κ ρ c : ℝ} (hκ : 0 < κ)
    (hW : ∀ l ε R : ℝ, 0 < ε → 4 * ε < l → 0 < R → l + 4 * ε ≤ ρ → R ≤ ρ →
      κ * (l + 4 * ε) < 1 / 4 → 4 * ε < κ * l ^ 2 → l < c * R ^ 2 / 9 →
      ∀ x ∈ f '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R), P x)
    {l ε R : ℝ} (hε : 0 < ε) (hl : 5 * ε < l) (hR : 0 < R) (hlρ : l + 5 * ε ≤ ρ)
    (hRρ : 5 * R / 4 ≤ ρ) (hκl : κ * (l + 5 * ε) < 1 / 4) (hεκ : 8 * ε < κ * l ^ 2)
    (hlR : l + ε / 8 < c * R ^ 2 / 16) :
    ∀ x ∈ f '' (PhaseCoordinates.closedStop l ε R ∪ PhaseCoordinates.closedSlat l ε R), P x := by
  rintro x ⟨u, hu, rfl⟩
  have hl0 : 0 < l := by linarith
  have hκε : 0 < κ * ε := mul_pos hκ hε
  have hc : 0 ≤ c := by
    by_contra h
    push_neg at h
    nlinarith [mul_pos (neg_pos.mpr h) (pow_pos hR 2)]
  have hcR : 0 ≤ c * R ^ 2 := mul_nonneg hc (sq_nonneg R)
  have hκl' : κ * l < 1 / 4 := by nlinarith
  have hκlε : κ * l * ε < ε / 4 := by nlinarith
  have hκε2 : 0 < κ * ε ^ 2 := mul_pos hκ (pow_pos hε 2)
  have hκlε0 : 0 < κ * l * ε := mul_pos (mul_pos hκ hl0) hε
  rcases closedCollar_subset_perturbed hε hR hu with (h | h) | h
  · exact hW _ _ _ (by positivity) (by linarith) (by positivity) (by linarith) (by linarith)
      (by nlinarith) (by nlinarith) (by nlinarith) _ ⟨u, h, rfl⟩
  · exact hW _ _ _ hε (by linarith) (by positivity) (by linarith) (by linarith)
      (by nlinarith) (by nlinarith) (by nlinarith) _ ⟨u, h, rfl⟩
  · exact hW _ _ _ hε (by linarith) (by positivity) (by linarith) (by linarith)
      (by nlinarith) (by nlinarith) (by nlinarith) _ ⟨u, h, rfl⟩

/-- CC3: the closed collar is compact in chart coordinates (proper fibre). -/
theorem closedCollar_isCompact {K : Type*} [NormedAddCommGroup K] [ProperSpace K] (l ε R : ℝ) :
    IsCompact (PhaseCoordinates.closedStop (K := K) l ε R ∪ PhaseCoordinates.closedSlat l ε R) := by
  refine ((isCompact_Icc (a := l + ε / 2) (b := l + 7 * ε / 2)).prod
    (isCompact_closedBall (0 : K) (7 * R / 8))).union ?_
  refine ((isCompact_Icc (a := -l + ε) (b := l + 7 * ε / 2)).prod
    (isCompact_closedBall (0 : K) (7 * R / 8))).of_isClosed_subset
    (isClosed_Icc.prod ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))) ?_
  rintro ⟨t, z⟩ ⟨ht, -, hz2⟩
  exact ⟨ht, mem_closedBall_zero_iff.mpr hz2⟩

/-- CC4: the closed room and the closed collar of an actual chart are compact in `R3`, and the
closed collar lies in the closed room. -/
theorem closedRooms_isCompact {θ : R3 → ℝ} {p : R3}
    (e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker)) {l ε R : ℝ}
    (hε : 0 < ε) (hl : 4 * ε < l) (hR : 0 < R)
    (hDt : PhaseCoordinates.closedD l ε R ⊆ e.target) :
    IsCompact (e.symm '' PhaseCoordinates.closedD l ε R) ∧
    IsCompact (e.symm '' (PhaseCoordinates.closedStop l ε R ∪ PhaseCoordinates.closedSlat l ε R)) ∧
    e.symm '' (PhaseCoordinates.closedStop l ε R ∪ PhaseCoordinates.closedSlat l ε R) ⊆
      e.symm '' PhaseCoordinates.closedD l ε R ∧
    e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R) ⊆
      e.symm '' (PhaseCoordinates.closedStop l ε R ∪ PhaseCoordinates.closedSlat l ε R) ∧
    e.symm '' PhaseCoordinates.roomD l ε R ⊆ e.symm '' PhaseCoordinates.closedD l ε R := by
  have hcs : PhaseCoordinates.closedStop l ε R ∪ PhaseCoordinates.closedSlat l ε R ⊆
      (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) := by
    rintro u (hu | hu)
    · exact PhaseCoordinates.roomD_subset_closedD (PhaseCoordinates.closedStop_subset_roomD
        hε hl hR hu)
    · exact PhaseCoordinates.roomD_subset_closedD (PhaseCoordinates.closedSlat_subset_roomD
        hε hl hR hu)
  have hcD : IsCompact (PhaseCoordinates.closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  refine ⟨hcD.image_of_continuousOn (e.continuousOn_symm.mono hDt),
    (closedCollar_isCompact l ε R).image_of_continuousOn
      (e.continuousOn_symm.mono (hcs.trans hDt)),
    Set.image_mono hcs, Set.image_mono ?_,
    Set.image_mono PhaseCoordinates.roomD_subset_closedD⟩
  rintro u (hu | hu)
  · exact Or.inl (PhaseCoordinates.roomStop_subset_closedStop hu)
  · exact Or.inr (PhaseCoordinates.roomSlat_subset_closedSlat hu)

end CompactCollar

section LocalizedRooms
open MeasureTheory

/-- LOC1: the native known-side rooms at `p` with a PRESCRIBED localization radius `r0`: the SAME
construction as `native_known_side_rooms_at`, additionally exporting `e.symm '' closedD ⊆ ball p r0`. -/
theorem native_known_side_rooms_loc (S : KnownSideSourceData) (g : MatrixField)
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
  obtain ⟨θ, hθ, h0, hd, c, hc, e, he, κ0, hκ0, H⟩ := native_room_interpolation_known_side_op
    g hg lam p hψ hψ0 hdψ (min r0 ((a - ‖lam • p‖) / lam)) (lt_min hr0 hr1) Q hQ
  refine ⟨θ, hθ, h0, hd, c, hc, e, he, κ0, hκ0, fun κ hκ hκ' => ?_⟩
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

/-- LOC2: NBA1 (actual native FIRST basis arm) on rooms localized in `ball p r0`. -/
theorem native_first_basis_arm_loc (S : KnownSideSourceData) :
    ∃ a1 : ℝ, 0 < a1 ∧ ∀ lam : ℝ, 0 < lam → ∀ r0 : ℝ, 0 < r0 → ∀ p : R3,
    lam • p ∈ Metric.ball (0 : R3) a1 → S.separating_function (lam • p) = 0 →
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧
      (∀ k, pd k θ p = pd k (fun x => -S.separating_function (lam • x)) p) ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
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
  obtain ⟨θ, hθ, h0, hd, c, hc, e, he, κ0, hκ0, H1⟩ := native_known_side_rooms_loc S S.g1
    S.g1_admissible lam hlam a1 hball hW p hp hp0 (hnc _ hp) r0 hr0
    (fun u x => coordinateFluxDivergence (metricDivergenceFlux (fun x => S.g1 (lam • x)) u) x)
    (fun u x h => (coordinateFluxDivergence_metricDivergenceFlux_eq_Lop _ u x).symm.trans h)
  refine ⟨θ, hθ, h0, hd, c, hc, e, he, κ0, hκ0, fun κ hκ hκ0' => ?_⟩
  obtain ⟨ρ, hρ, H2⟩ := H1 κ hκ hκ0'
  refine ⟨ρ, hρ, fun l ε R hε hl hR hlρ hRρ hκh hε4 hlR => ?_⟩
  obtain ⟨hloc, hDt, hroom, hW', Kint, hKint, HI⟩ := H2 l ε R hε hl hR hlρ hRρ hκh hε4 hlR
  obtain ⟨hDo, hOD, hSD⟩ := native_room_open_subsets e hε hl hR hDt
  have hκl : κ * l ≤ 1 / 4 := by nlinarith [mul_pos hκ hε]
  obtain ⟨-, -, hg1, hg2⟩ := strictExponent_bounds hκ (by linarith) hκl hε.le hε4
  exact ⟨hloc, hDt, hDo, hOD, hSD, hroom, hW', hg1, hg2, Kint, hKint,
    first_basis_arm_on_of_room S lam _ _ _ HI⟩

/-- LOC3: NBA2 (actual native SECOND coefficient arm, both normalizations) on rooms localized in
`ball p r0`. -/
theorem native_second_coefficient_arm_loc (S : KnownSideSourceData) (L : ℝ) :
    ∃ a1 : ℝ, 0 < a1 ∧ ∀ lam : ℝ, 0 < lam → ∀ r0 : ℝ, 0 < r0 → ∀ p : R3,
    lam • p ∈ Metric.ball (0 : R3) a1 → S.separating_function (lam • p) = 0 →
    ∃ θ : R3 → ℝ, ContDiff ℝ ∞ θ ∧ θ p = 0 ∧
      (∀ k, pd k θ p = pd k (fun x => -S.separating_function (lam • x)) p) ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker),
      (∀ x, e x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x - p))) ∧
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
  obtain ⟨θ, hθ, h0, hd, c, hc, e, he, κ0, hκ0, H1⟩ := native_known_side_rooms_loc S S.g2
    S.g2_admissible lam hlam a1 hball hW p hp hp0 (hnc _ hp) r0 hr0
    (fun u x => normalizedSecondLaplacian S.g1 S.g2 L lam u x)
    (fun u x h => (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2 S.g1_admissible
      S.g2_admissible L lam u x).mp h)
  refine ⟨θ, hθ, h0, hd, c, hc, e, he, κ0, hκ0, fun κ hκ hκ0' => ?_⟩
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

end LocalizedRooms

section CommonPair
open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise

/-- PC: closed rooms over the coordinate room, closed collars over `W`, disjoint rooms: both cross
products lie in the ORIGINAL initial cross. -/
theorem pair_cross_subset (S : KnownSideSourceData) (lam : ℝ) {A1 C1 A2 C2 : Set R3}
    (hA1 : ∀ x ∈ A1, lam • x ∈ S.coordinateRoom) (hA2 : ∀ y ∈ A2, lam • y ∈ S.coordinateRoom)
    (hC1 : C1 ⊆ A1) (hC2 : C2 ⊆ A2) (hC1W : ∀ x ∈ C1, lam • x ∈ S.W)
    (hC2W : ∀ y ∈ C2, lam • y ∈ S.W) (hdisj : Disjoint A1 A2) :
    C1 ×ˢ A2 ⊆ initialCross S lam ∧ A1 ×ˢ C2 ⊆ initialCross S lam := by
  constructor
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨⟨hA1 x (hC1 hx), hA2 y hy, fun hxy => hdisj.ne_of_mem (hC1 hx) hy hxy⟩,
      Or.inl (hC1W x hx)⟩
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨⟨hA1 x hx, hA2 y (hC2 hy), fun hxy => hdisj.ne_of_mem hx (hC2 hy) hxy⟩,
      Or.inr (hC2W y hy)⟩

/-- SP: slack room parameters (CC2 hypotheses, which imply the original eight) exist. -/
theorem exists_slack_params {κ ρ c : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (hc : 0 < c) :
    ∃ l ε R : ℝ, 0 < ε ∧ 5 * ε < l ∧ 0 < R ∧ l + 5 * ε ≤ ρ ∧ 5 * R / 4 ≤ ρ ∧
      κ * (l + 5 * ε) < 1 / 4 ∧ 8 * ε < κ * l ^ 2 ∧ l + ε / 8 < c * R ^ 2 / 16 := by
  have hR : 0 < 4 * ρ / 5 := by positivity
  have hcR : 0 < c * (4 * ρ / 5) ^ 2 := by positivity
  obtain ⟨l, hl, hl1, hl2, hl3⟩ : ∃ l : ℝ, 0 < l ∧ l ≤ ρ / 2 ∧ l ≤ 1 / (16 * κ) ∧
      l ≤ c * (4 * ρ / 5) ^ 2 / 64 :=
    ⟨min (ρ / 2) (min (1 / (16 * κ)) (c * (4 * ρ / 5) ^ 2 / 64)),
      lt_min (by positivity) (lt_min (by positivity) (by positivity)), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hκl : κ * l ≤ 1 / 16 := by
    rw [le_div_iff₀ (by positivity)] at hl2
    nlinarith
  have hq : κ * l ^ 2 ≤ l / 16 := by nlinarith
  have hq0 : 0 < κ * l ^ 2 := by positivity
  have hκl2 : (κ * l) ^ 2 ≤ 1 / 256 := by nlinarith [mul_pos hκ hl]
  refine ⟨l, κ * l ^ 2 / 16, 4 * ρ / 5, by positivity, by nlinarith, hR, by nlinarith,
    by linarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- Name of the EXACT second-coefficient interpolation premise, for elaboration only. -/
def SecondCoefficientInterpolationOn (S : KnownSideSourceData) (L lam : ℝ)
    (D2 O2 S2 : Set R3) (K2i γ2 : ℝ) : Prop :=
  ∀ (b : R3 → ℝ), ContDiffOn ℝ ∞ b D2 →
      (∀ x ∈ D2, normalizedSecondLaplacian S.g1 S.g2 L lam b x = 0) →
      ∀ (bD : Lp ℝ 2 ((volume : Measure R3).restrict D2))
        (bO : Lp ℝ 2 ((volume : Measure R3).restrict O2))
        (bS : Lp ℝ 2 ((volume : Measure R3).restrict S2)),
      b =ᵐ[(volume : Measure R3).restrict D2] (bD : R3 → ℝ) →
      b =ᵐ[(volume : Measure R3).restrict O2] (bO : R3 → ℝ) →
      b =ᵐ[(volume : Measure R3).restrict S2] (bS : R3 → ℝ) →
      ∀ M μ : ℝ, 0 < μ → 0 ≤ M → ‖bS‖ ≤ M → ‖bD‖ ≤ M / μ →
        ‖bO‖ ≤ K2i * M * μ ^ (γ2 - 1)

/-- Name (statement only): the SAME restricted first-harmonic family `i ↦ R_U wᵢ`. -/
def firstRestrictFamily (S : KnownSideSourceData) (lam : ℝ) (D1 : Set R3) (hD1 : IsOpen D1)
    (U : Set R3) (hUD1 : U ⊆ D1) {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (i : ι) :
    Lp ℝ 2 ((volume : Measure R3).restrict U) :=
  harmonicRestrict D1 hD1 (dilatedFirstPrincipal S lam)
    (contDiff_dilatedFirstPrincipal S lam).contDiffOn U hUD1 (w i)

/-- Name (statement only): the ACTUAL unnormalized coefficient
`bᵢ = initialCoefficient S lam T μᵢ (R_T wᵢ)`. -/
def actualSecondCoefficient (S : KnownSideSourceData) (lam : ℝ) (D1 : Set R3) (hD1 : IsOpen D1)
    (T : Set R3) (hTD1 : T ⊆ D1) {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ) (i : ι) : R3 → ℝ :=
  initialCoefficient S lam T (μ i) (firstRestrictFamily S lam D1 hD1 T hTD1 w i)

/-- Name (statement only) of the cross-tensor output on `O1 × O2` for ONE constant `M`: the
unnormalized classes `gᵢ = [bᵢ]_{O2}`, both arm bounds, `γ₁+γ₂-1 > 0`, tensor summability. -/
def CrossTensorOn (S : KnownSideSourceData) (lam : ℝ) (D1 : Set R3) (hD1 : IsOpen D1)
    (O1 : Set R3) (hO1D1 : O1 ⊆ D1) (T : Set R3) (hTD1 : T ⊆ D1) (O2 : Set R3)
    (K1i K2i γ1 γ2 M : ℝ) {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ) : Prop :=
  ∃ g : ι → Lp ℝ 2 ((volume : Measure R3).restrict O2),
    (∀ i, actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i
      =ᵐ[(volume : Measure R3).restrict O2] (g i : R3 → ℝ)) ∧
    (∀ i, ‖g i‖ ≤ K2i * M * μ i ^ (γ2 - 1)) ∧
    (∀ i, ‖firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i‖ ≤ K1i * μ i ^ γ1) ∧
    0 < γ1 + γ2 - 1 ∧
    Summable fun i => tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i)

/-- Name (statement only) of the full CP-B output on the SAME singular family `(ι, w, μ)`. -/
def CrossSeriesOn (S : KnownSideSourceData) (L lam : ℝ) (D1 : Set R3) (hD1 : IsOpen D1)
    (O1 : Set R3) (hO1D1 : O1 ⊆ D1) (T : Set R3) (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3)
    (K1i K2i γ1 γ2 : ℝ) (ι : Type)
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ) : Prop :=
  ActualSingularSystem S lam D1 hD1 T hTD1 ι w μ ∧ (∀ i, μ i ≤ 1) ∧
    (∀ β : ℝ, 0 < β → Summable fun i => μ i ^ β) ∧
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ i, SecondCoefficientArmsOn S L lam D2 S2 M (μ i)
        (actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i)) ∧
      CrossTensorOn S lam D1 hD1 O1 hO1D1 T hTD1 O2 K1i K2i γ1 γ2 M w μ

/-- CP-B1: for ANY family `b` with both coefficient arms on `D2`/`S2`, the exact second
interpolation premise gives the unnormalized `O2` classes with `‖[bᵢ]_{O2}‖ ≤ K₂ M μᵢ^(γ₂-1)`. -/
theorem second_classes_of_arms (S : KnownSideSourceData) (L lam : ℝ) {D2 O2 S2 : Set R3}
    (hO2D2 : O2 ⊆ D2) {K2i γ2 M : ℝ} (hM : 0 ≤ M)
    (HB : SecondCoefficientInterpolationOn S L lam D2 O2 S2 K2i γ2)
    {ι : Type} (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i) (b : ι → R3 → ℝ)
    (harms : ∀ i, SecondCoefficientArmsOn S L lam D2 S2 M (μ i) (b i)) :
    ∃ g : ι → Lp ℝ 2 ((volume : Measure R3).restrict O2),
      (∀ i, b i =ᵐ[(volume : Measure R3).restrict O2] (g i : R3 → ℝ)) ∧
      ∀ i, ‖g i‖ ≤ K2i * M * μ i ^ (γ2 - 1) := by
  have H : ∀ i, ∃ gi : Lp ℝ 2 ((volume : Measure R3).restrict O2),
      b i =ᵐ[(volume : Measure R3).restrict O2] (gi : R3 → ℝ) ∧
      ‖gi‖ ≤ K2i * M * μ i ^ (γ2 - 1) := by
    intro i
    obtain ⟨hsm, hpde, ⟨hbD, hbDn⟩, ⟨hbS, hbSn⟩⟩ := harms i
    have hbO : MemLp (b i) 2 ((volume : Measure R3).restrict O2) :=
      hbD.mono_measure (Measure.restrict_mono hO2D2 le_rfl)
    exact ⟨hbO.toLp (b i), hbO.coeFn_toLp.symm,
      HB (b i) hsm hpde (hbD.toLp (b i)) (hbO.toLp (b i)) (hbS.toLp (b i))
        hbD.coeFn_toLp.symm hbO.coeFn_toLp.symm hbS.coeFn_toLp.symm M (μ i) (hμ i) hM hbSn hbDn⟩
  choose g hg1 hg2 using H
  exact ⟨g, hg1, hg2⟩

/-- CP-B2: on the SAME singular family, the first basis arm, the arms of the actual `bᵢ` and the
second interpolation premise give the cross-tensor output (CS1 on `fᵢ = R_{O1} wᵢ`, `gᵢ = [bᵢ]_{O2}`). -/
theorem crossTensorOn_of_arms (S : KnownSideSourceData) (L lam : ℝ) (D1 : Set R3)
    (hD1 : IsOpen D1) (O1 : Set R3) (hO1D1 : O1 ⊆ D1) (T : Set R3) (hTD1 : T ⊆ D1)
    (D2 O2 S2 : Set R3) (hO2D2 : O2 ⊆ D2) {K1i K2i γ1 γ2 M : ℝ} (hK1i : 0 < K1i) (hM : 0 ≤ M)
    (hγ1 : 1 / 2 < γ1) (hγ2 : 1 / 2 < γ2)
    (HA : FirstBasisArmOn S lam D1 O1 T K1i γ1)
    (HB : SecondCoefficientInterpolationOn S L lam D2 O2 S2 K2i γ2) {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (hsys : ActualSingularSystem S lam D1 hD1 T hTD1 ι w μ)
    (hsum : ∀ β : ℝ, 0 < β → Summable fun i => μ i ^ β)
    (harms : ∀ i, SecondCoefficientArmsOn S L lam D2 S2 M (μ i)
      (actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i)) :
    CrossTensorOn S lam D1 hD1 O1 hO1D1 T hTD1 O2 K1i K2i γ1 γ2 M w μ := by
  obtain ⟨hμ, -, hgram⟩ := hsys
  obtain ⟨g, hgae, hg⟩ := second_classes_of_arms S L lam hO2D2 hM HB μ hμ
    (actualSecondCoefficient S lam D1 hD1 T hTD1 w μ) harms
  have hf : ∀ i, ‖firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i‖ ≤ K1i * μ i ^ γ1 :=
    HA hD1 hO1D1 hTD1 ι w μ hμ hgram
  obtain ⟨hγ, hs⟩ := cross_tensor_summable_of_strict
    (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w) g μ hμ hK1i.le hf hg hγ1 hγ2 hsum
  exact ⟨g, hgae, hg, hf, hγ, hs⟩

/-- CP-B: the ACTUAL cross tensor series on ONE common pair of native rooms. From the room facts
(produced by LOC2/LOC3/CC/PC), the SAME spectral system of `R_T` (`harmonicRestrict_summable_spectral_data`),
the first basis arm, both coefficient bounds (SF) and the second arm give the unnormalized
coefficient classes `gᵢ = [bᵢ]_{O2}` with `‖gᵢ‖ ≤ K₂ M μᵢ^(γ₂-1)` and L²(O1×O2)-summable tensors
(`CrossSeriesOn` unfolds verbatim to the v028 conclusion). -/
theorem cross_series_of_rooms (S : KnownSideSourceData) (L lam : ℝ) (hlam : 0 < lam)
    (D1 O1 T K1 KT D2 O2 S2 J2 JS : Set R3) (hD1 : IsOpen D1) (hconn : IsConnected D1)
    (hO1D1 : O1 ⊆ D1) (hT : IsOpen T) (hTne : T.Nonempty) (hKT : IsCompact KT)
    (hTKT : T ⊆ KT) (hKTD1 : KT ⊆ D1) (hTD1 : T ⊆ D1) (hK1 : IsCompact K1) (hD1K1 : D1 ⊆ K1)
    (hD2 : IsOpen D2) (hO2D2 : O2 ⊆ D2) (hS2 : IsOpen S2) (hJ2 : IsCompact J2)
    (hD2J2 : D2 ⊆ J2) (hJS : IsCompact JS) (hS2JS : S2 ⊆ JS)
    (hrow : KT ×ˢ J2 ⊆ initialCross S lam) (hobs : K1 ×ˢ JS ⊆ initialCross S lam)
    {K1i K2i γ1 γ2 : ℝ} (hK1i : 0 < K1i) (hγ1 : 1 / 2 < γ1) (hγ2 : 1 / 2 < γ2)
    (HA : FirstBasisArmOn S lam D1 O1 T K1i γ1)
    (HB : SecondCoefficientInterpolationOn S L lam D2 O2 S2 K2i γ2) :
    ∃ (ι : Type) (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
        (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ),
      CrossSeriesOn S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ := by
  obtain ⟨ι, w, μ, hμ, hμ1, heigen, hgram, hsum⟩ := harmonicRestrict_summable_spectral_data
    D1 hD1 hconn (dilatedFirstPrincipal S lam) (contDiff_dilatedFirstPrincipal S lam).contDiffOn
    (fun x _ => dilatedFirstPrincipal_posDef S lam x) T hT hTne KT hKT hTKT hKTD1
  have hsys : ActualSingularSystem S lam D1 hD1 T hTD1 ι w μ := ⟨hμ, heigen, hgram⟩
  obtain ⟨M, hM, HSF⟩ := actualCoefficient_both_bounds S L lam hlam D1 K1 T KT D2 J2 S2 JS hD1
    hK1 hD1K1 hT hKT hTKT hTD1 hD2 hJ2 hD2J2 hS2 hJS hS2JS hrow hobs
  have harms : ∀ i, SecondCoefficientArmsOn S L lam D2 S2 M (μ i)
      (actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i) := HSF ι w μ hsys
  exact ⟨ι, w, μ, hsys, hμ1, hsum, M, hM, harms,
    crossTensorOn_of_arms S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 hO2D2 hK1i hM hγ1 hγ2 HA HB
      w μ hsys hsum harms⟩

/-- NCP-a: the chart-room facts needed by CP-B, from `closedD ⊆ e.target` alone: openness,
connectedness of `D`, nonemptiness of the collar, compact buffers and their inclusions. -/
theorem chart_room_facts {θ : R3 → ℝ} {p : R3}
    (e : OpenPartialHomeomorph R3 (ℝ × (fderiv ℝ θ p).ker)) {l ε R : ℝ}
    (hε : 0 < ε) (hl : 4 * ε < l) (hR : 0 < R)
    (hDt : PhaseCoordinates.closedD l ε R ⊆ e.target) :
    IsConnected (e.symm '' PhaseCoordinates.roomD l ε R) ∧
    IsOpen (e.symm '' PhaseCoordinates.roomO l ε R) ∧
    IsOpen (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)) ∧
    (e.symm '' (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R)).Nonempty ∧
    e.symm '' (PhaseCoordinates.closedStop l ε R ∪ PhaseCoordinates.closedSlat l ε R) ⊆
      e.symm '' PhaseCoordinates.roomD l ε R := by
  have hDT : (PhaseCoordinates.roomD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆ e.target :=
    PhaseCoordinates.roomD_subset_closedD.trans hDt
  have hcol : PhaseCoordinates.closedStop l ε R ∪ PhaseCoordinates.closedSlat l ε R ⊆
      (PhaseCoordinates.roomD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) := by
    rintro u (hu | hu)
    · exact PhaseCoordinates.closedStop_subset_roomD hε hl hR hu
    · exact PhaseCoordinates.closedSlat_subset_roomD hε hl hR hu
  have hSD : PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R ⊆
      (PhaseCoordinates.roomD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) := by
    rintro u (hu | hu)
    · exact hcol (Or.inl (PhaseCoordinates.roomStop_subset_closedStop hu))
    · exact hcol (Or.inr (PhaseCoordinates.roomSlat_subset_closedSlat hu))
  have hl0 : 0 < l := by linarith
  have hconv : Convex ℝ (PhaseCoordinates.roomD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) :=
    (convex_Ioo _ _).prod (convex_ball _ _)
  have hne : (PhaseCoordinates.roomD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)).Nonempty :=
    ⟨(0, 0), Set.mk_mem_prod ⟨by linarith, by linarith⟩ (Metric.mem_ball_self hR)⟩
  have hOo : IsOpen (PhaseCoordinates.roomO l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) :=
    isOpen_Ioo.prod Metric.isOpen_ball
  have hSo : IsOpen (PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R :
      Set (ℝ × (fderiv ℝ θ p).ker)) :=
    (isOpen_Ioo.prod Metric.isOpen_ball).union (isOpen_Ioo.prod
      ((isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)))
  have hmem : ((l + ε, 0) : ℝ × (fderiv ℝ θ p).ker) ∈
      PhaseCoordinates.roomStop l ε R ∪ PhaseCoordinates.roomSlat l ε R :=
    Or.inl (Set.mk_mem_prod ⟨by linarith, by linarith⟩ (Metric.mem_ball_self (by positivity)))
  refine ⟨(hconv.isConnected hne).image _ (e.continuousOn_symm.mono hDT),
    e.isOpen_image_symm_of_subset_target hOo
      ((PhaseCoordinates.roomO_subset_closedO.trans
        (PhaseCoordinates.closedO_subset_roomD hε hl hR)).trans hDT),
    e.isOpen_image_symm_of_subset_target hSo (hSD.trans hDT),
    ⟨_, Set.mem_image_of_mem _ hmem⟩, Set.image_mono hcol⟩

/-- NCP-b: SP slack parameters for `(κ, ρ, c)` are admissible (original eight conditions) and
CC2-slack for every LARGER `ρ' ≥ ρ`, `c' ≥ c`. -/
theorem slack_params_mono {κ ρ c ρ' c' l ε R : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ ρ') (hc : c ≤ c')
    (hε : 0 < ε) (hl5 : 5 * ε < l) (hR : 0 < R) (hlρ : l + 5 * ε ≤ ρ) (hRρ : 5 * R / 4 ≤ ρ)
    (hκl : κ * (l + 5 * ε) < 1 / 4) (hεκ : 8 * ε < κ * l ^ 2)
    (hlR : l + ε / 8 < c * R ^ 2 / 16) :
    (4 * ε < l ∧ l + 4 * ε ≤ ρ' ∧ R ≤ ρ' ∧ κ * (l + 4 * ε) < 1 / 4 ∧ 4 * ε < κ * l ^ 2 ∧
      l < c' * R ^ 2 / 9) ∧
    (l + 5 * ε ≤ ρ' ∧ 5 * R / 4 ≤ ρ' ∧ l + ε / 8 < c' * R ^ 2 / 16) := by
  have hcc : c * R ^ 2 ≤ c' * R ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg R)
  have hκε : 0 < κ * ε := mul_pos hκ hε
  refine ⟨⟨by linarith, by linarith, by linarith, by nlinarith, by linarith, by linarith⟩,
    by linarith, by linarith, by linarith⟩

/-- Name (statement only) of the exported facts of ONE common native pair of rooms. -/
def CommonPairFacts (S : KnownSideSourceData) (lam r0 : ℝ) (p1 p2 : R3)
    (D1 O1 T D2 O2 S2 : Set R3) (K1i K2i γ1 γ2 : ℝ) : Prop :=
  D1 ⊆ Metric.ball p1 r0 ∧ D2 ⊆ Metric.ball p2 r0 ∧ Disjoint D1 D2 ∧
  IsOpen D1 ∧ IsConnected D1 ∧ IsOpen O1 ∧ O1 ⊆ D1 ∧ IsOpen T ∧ T.Nonempty ∧ T ⊆ D1 ∧
  IsOpen D2 ∧ IsOpen O2 ∧ O2 ⊆ D2 ∧ IsOpen S2 ∧ S2 ⊆ D2 ∧
  (∀ x ∈ D1, lam • x ∈ S.coordinateRoom) ∧ (∀ y ∈ D2, lam • y ∈ S.coordinateRoom) ∧
  (∀ x ∈ T, lam • x ∈ S.W) ∧ (∀ y ∈ S2, lam • y ∈ S.W) ∧
  0 < K1i ∧ 0 < K2i ∧ 1 / 2 < γ1 ∧ γ1 < 1 ∧ 1 / 2 < γ2 ∧ γ2 < 1

/-- NCP-c: ONE ACTUAL common native pair. At two scaled boundary points with `2 r0 ≤ dist p1 p2`,
the localized FIRST rooms at `p1` and SECOND rooms at `p2`, with the SAME `κ` and the SAME slack
`(l, ε, R)`, carry the actual cross tensor series (`cross_series_of_rooms` on these witnesses). -/
theorem native_common_pair (S : KnownSideSourceData) (L : ℝ) :
    ∃ a1 : ℝ, 0 < a1 ∧ ∀ lam : ℝ, 0 < lam → ∀ r0 : ℝ, 0 < r0 → ∀ p1 p2 : R3,
    lam • p1 ∈ Metric.ball (0 : R3) a1 → S.separating_function (lam • p1) = 0 →
    lam • p2 ∈ Metric.ball (0 : R3) a1 → S.separating_function (lam • p2) = 0 →
    r0 + r0 ≤ dist p1 p2 →
    ∃ (D1 : Set R3) (hD1 : IsOpen D1) (O1 : Set R3) (hO1D1 : O1 ⊆ D1) (T : Set R3)
      (hTD1 : T ⊆ D1) (D2 O2 S2 : Set R3) (K1i K2i γ1 γ2 : ℝ),
      CommonPairFacts S lam r0 p1 p2 D1 O1 T D2 O2 S2 K1i K2i γ1 γ2 ∧
      SecondCoefficientInterpolationOn S L lam D2 O2 S2 K2i γ2 ∧
      FirstBasisArmOn S lam D1 O1 T K1i γ1 ∧
      ∃ (ι : Type) (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
          (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ),
        CrossSeriesOn S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ := by
  obtain ⟨a1, ha1, H1⟩ := native_first_basis_arm_loc S
  obtain ⟨a2, ha2, H2⟩ := native_second_coefficient_arm_loc S L
  refine ⟨min a1 a2, lt_min ha1 ha2,
    fun lam hlam r0 hr0 p1 p2 hp1 hp10 hp2 hp20 hsep => ?_⟩
  obtain ⟨θ1, -, -, -, c1, hc1, e1, -, κ1, hκ1, F1⟩ := H1 lam hlam r0 hr0 p1
    (Metric.ball_subset_ball (min_le_left _ _) hp1) hp10
  obtain ⟨θ2, -, -, -, c2, hc2, e2, -, κ2, hκ2, F2⟩ := H2 lam hlam r0 hr0 p2
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
  obtain ⟨-, hO2o, hS2o, -, -⟩ := chart_room_facts e2 hε hl hR hDt2
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
    ⟨fun x hx => hloc1 (hD1K1 hx), fun y hy => hloc2 (hD2J2 hy),
      hdisj.mono hD1K1 hD2J2, hDo1, hconn, hO1o, hOD1, hTo, hTne, hSD1, hDo2, hO2o, hOD2, hS2o,
      hSD2, fun x hx => hroom1 x (hD1K1 hx), fun y hy => hroom2 y (hD2J2 hy),
      fun x hx => hKTW x (hTKT hx), fun y hy => hJSW y (hS2JS hy),
      hK1i, hK2i, hg11, hg12, hg21, hg22⟩, HB, HA, ι, w, μ, hser⟩

/-- CL-a: a summable tensor series has its `tsum` as HasSum limit, reached along ONE monotone
cofinal finset sequence of the SAME indices; each partial sum is a.e. the pointwise cross sum. -/
theorem tensor_series_cofinal_limit {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {m : Measure α} {n : Measure β} [SFinite m] [SFinite n] {ι : Type*}
    (f : ι → Lp ℝ 2 m) (g : ι → Lp ℝ 2 n) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (hsum : ∀ b : ℝ, 0 < b → Summable fun i => μ i ^ b)
    (hs : Summable fun i => tensorLp (f i) (g i)) :
    ∃ s : ℕ → Finset ι, Monotone s ∧ Tendsto s atTop atTop ∧
      HasSum (fun i => tensorLp (f i) (g i)) (∑' i, tensorLp (f i) (g i)) ∧
      Tendsto (fun k => ∑ i ∈ s k, tensorLp (f i) (g i)) atTop
        (𝓝 (∑' i, tensorLp (f i) (g i))) ∧
      ∀ k, ((∑ i ∈ s k, tensorLp (f i) (g i) : Lp ℝ 2 (m.prod n)) : α × β → ℝ) =ᵐ[m.prod n]
        fun z => ∑ i ∈ s k, f i z.1 * g i z.2 := by
  obtain ⟨s, hmono, hcof⟩ := exists_cofinal_of_spectral_rpow hμ hsum
  have hH : Tendsto (fun t : Finset ι => ∑ i ∈ t, tensorLp (f i) (g i)) atTop
      (𝓝 (∑' i, tensorLp (f i) (g i))) := hs.hasSum
  exact ⟨s, hmono, hcof, hs.hasSum, hH.comp hcof, fun k => tensorLp_finset_sum_ae (s k) f g⟩

/-- CL-b: the ACTUAL same-series L² limit on `O1 × O2`: the SAME `M`, classes `gᵢ = [bᵢ]_{O2}`,
ONE cofinal finset sequence, HasSum to the `tsum`, convergence of the SAME partial sums, and each
partial sum a.e. equal to `∑ (R_{O1} wᵢ)(x) bᵢ(y)` with the ACTUAL unnormalized coefficients. -/
theorem crossSeries_actual_limit (S : KnownSideSourceData) (L lam : ℝ) (D1 : Set R3)
    (hD1 : IsOpen D1) (O1 : Set R3) (hO1D1 : O1 ⊆ D1) (T : Set R3) (hTD1 : T ⊆ D1)
    (D2 O2 S2 : Set R3) {K1i K2i γ1 γ2 : ℝ} {ι : Type}
    (w : HilbertBasis ι ℝ (harmonicSub D1 hD1 (dilatedFirstPrincipal S lam)
      (contDiff_dilatedFirstPrincipal S lam).contDiffOn)) (μ : ι → ℝ)
    (h : CrossSeriesOn S L lam D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 K1i K2i γ1 γ2 ι w μ) :
    ∃ (M : ℝ) (g : ι → Lp ℝ 2 ((volume : Measure R3).restrict O2)) (s : ℕ → Finset ι),
      0 ≤ M ∧ (∀ i, actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i
        =ᵐ[(volume : Measure R3).restrict O2] (g i : R3 → ℝ)) ∧
      (∀ i, ‖g i‖ ≤ K2i * M * μ i ^ (γ2 - 1)) ∧
      Monotone s ∧ Tendsto s atTop atTop ∧
      HasSum (fun i => tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i))
        (∑' i, tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i)) ∧
      Tendsto (fun k => ∑ i ∈ s k,
          tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i)) atTop
        (𝓝 (∑' i, tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i))) ∧
      ∀ k, ((∑ i ∈ s k, tensorLp (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i) (g i) :
          Lp ℝ 2 (((volume : Measure R3).restrict O1).prod ((volume : Measure R3).restrict O2))) :
          R3 × R3 → ℝ)
        =ᵐ[((volume : Measure R3).restrict O1).prod ((volume : Measure R3).restrict O2)]
        fun z => ∑ i ∈ s k, (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w i : R3 → ℝ) z.1 *
          actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i z.2 := by
  obtain ⟨⟨hμ, -, -⟩, -, hsum, M, hM, -, g, hgae, hg, -, -, hs⟩ := h
  obtain ⟨s, hmono, hcof, hH, hT, hae⟩ := tensor_series_cofinal_limit
    (firstRestrictFamily S lam D1 hD1 O1 hO1D1 w) g μ hμ hsum hs
  refine ⟨M, g, s, hM, hgae, hg, hmono, hcof, hH, hT, fun k => ?_⟩
  have hb : ∀ᵐ z ∂(((volume : Measure R3).restrict O1).prod ((volume : Measure R3).restrict O2)),
      ∀ i ∈ s k, actualSecondCoefficient S lam D1 hD1 T hTD1 w μ i z.2 = (g i : R3 → ℝ) z.2 :=
    (eventually_all_finset (s k)).2 fun i _ =>
      Measure.quasiMeasurePreserving_snd.ae_eq_comp (hgae i)
  filter_upwards [hae k, hb] with z hz hzb
  rw [hz]
  exact Finset.sum_congr rfl fun i hi => by rw [hzb i hi]

end CommonPair

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
