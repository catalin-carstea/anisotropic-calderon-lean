import MixedKernelNativeKnownSideGeometry
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
open Set Metric Filter
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable
open Set MeasureTheory
open scoped ContDiff Topology
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open Geometry


section FixedSeparationRoom

/-- FS1: the dilated off-diagonal room is open for every `lam`. -/
theorem dilatedOffDiagonal_isOpen (S : KnownSideSourceData) (lam : ℝ) :
    IsOpen (dilatedOffDiagonal S lam) := by
  have h1 : IsOpen {v : R3 × R3 | lam • v.1 ∈ S.coordinateRoom} :=
    S.coordinateRoom_open.preimage (continuous_fst.const_smul lam)
  have h2 : IsOpen {v : R3 × R3 | lam • v.2 ∈ S.coordinateRoom} :=
    S.coordinateRoom_open.preimage (continuous_snd.const_smul lam)
  have h3 : IsOpen {v : R3 × R3 | v.1 ≠ v.2} := isOpen_ne_fun continuous_fst continuous_snd
  exact h1.inter (h2.inter h3)

/-- FS3: the compact cylinder lies in the closed ball of radius `2`. -/
theorem cylinder_norm_le {y : R3} (hy : y ∈ cylinder) : ‖y‖ ≤ 2 := by
  have hy' : y 0 ^ 2 + y 1 ^ 2 ≤ 1 ∧ (-1 : ℝ) ≤ y 2 ∧ y 2 ≤ 1 := hy
  obtain ⟨h01, h2a, h2b⟩ := hy'
  have hsq : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  have h2 : y 2 ^ 2 ≤ 1 := by nlinarith
  nlinarith [norm_nonneg y]

/-- FS2: ONE open neighbourhood of the fixed-separation set and ONE dilation threshold, both
chosen from `S, bound, separation` only (before `lam`), inside every dilated off-diagonal room. -/
theorem exists_fixedSeparation_room (S : KnownSideSourceData) {bound separation : ℝ}
    (hb : 0 < bound) (hs : 0 < separation) :
    ∃ lamB : ℝ, 0 < lamB ∧ ∃ U : Set (R3 × R3), IsOpen U ∧
      fixedSeparationSet bound separation ⊆ U ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ lamB → U ⊆ dilatedOffDiagonal S lam := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp S.coordinateRoom_open 0 S.origin_mem
  have hB : 0 < bound + 2 := by linarith
  refine ⟨r / (2 * (bound + 2)), by positivity,
    {v | ‖v.1‖ < bound + 1 ∧ ‖v.2‖ < bound + 1 ∧ separation / 2 < ‖v.1 - v.2‖}, ?_, ?_, ?_⟩
  · exact (isOpen_lt continuous_fst.norm continuous_const).inter
      ((isOpen_lt continuous_snd.norm continuous_const).inter
        (isOpen_lt continuous_const (continuous_fst.sub continuous_snd).norm))
  · rintro v ⟨h1, h2, h3⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro lam hlam hlamB v ⟨h1, h2, h3⟩
    have hlr : lam * (2 * (bound + 2)) ≤ r :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (bound + 2))).mp hlamB
    have hsm : ∀ w : R3, ‖w‖ < bound + 1 → lam • w ∈ S.coordinateRoom := by
      intro w hw
      apply hball
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
      have hlt : lam * ‖w‖ ≤ lam * (bound + 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hlam.le
      have hpos : 0 < lam * (bound + 2) := mul_pos hlam hB
      nlinarith
    refine ⟨hsm _ h1, hsm _ h2, fun heq => ?_⟩
    rw [heq, sub_self, norm_zero] at h3
    linarith

end FixedSeparationRoom

section NativeProductUCP
open scoped Matrix.Norms.Elementwise

/-- NUCP-b: the bare principal `Lop` is literally the supplied `divCoeffGrad`. -/
theorem Lop_eq_divCoeffGrad (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (u : R3 → ℝ) (x : R3) :
    Lop (fun i k y => A y i k) u x = divCoeffGrad A u x := rfl

/-- NUCP-c: linearity of `divCoeffGrad` on a difference, from the supplied jet lemmas. -/
theorem divCoeffGrad_sub_eq_zero {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} {u v : R3 → ℝ} {x : R3}
    (hA : DifferentiableAt ℝ A x) (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x)
    (hLu : divCoeffGrad A u x = 0) (hLv : divCoeffGrad A v x = 0) :
    divCoeffGrad A (fun z => u z - v z) x = 0 := by
  have e : (fun z => u z - v z) = u + (-1 : ℝ) • v := by
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, Regularity.Jets.divCoeffGrad_add hA hu
      (show ContDiffAt ℝ 2 ((-1 : ℝ) • v) x from hv.const_smul (-1 : ℝ)),
    Regularity.Jets.divCoeffGrad_smul (-1 : ℝ) hA hv, hLu, hLv]
  norm_num

/-- NUCP: the SUPPLIED product unique continuation applied exactly to the two literal native
operators of `ProductSolutionOn`: two native product solutions on a connected open box that agree
on a nonempty open sub-box agree on the whole box. -/
theorem native_product_eq_of_eq_on_box (S : KnownSideSourceData) (L lam : ℝ)
    {U V U0 V0 : Set R3} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) {F G : R3 × R3 → ℝ}
    (hF : ProductSolutionOn S L lam F (U ×ˢ V)) (hG : ProductSolutionOn S L lam G (U ×ˢ V))
    (hU0 : IsOpen U0) (hU0n : U0.Nonempty) (hU0U : U0 ⊆ U)
    (hV0 : IsOpen V0) (hV0n : V0.Nonempty) (hV0V : V0 ⊆ V)
    (hEq : ∀ x ∈ U0, ∀ y ∈ V0, F (x, y) = G (x, y)) :
    ∀ x ∈ U, ∀ y ∈ V, F (x, y) = G (x, y) := by
  set A : R3 → Matrix (Fin 3) (Fin 3) ℝ := fun x => principalCoefficient S.g1 (lam • x) with hAdef
  set B : R3 → Matrix (Fin 3) (Fin 3) ℝ := fun y => principalCoefficient S.g2 (lam • y) with hBdef
  have hAc : ContDiff ℝ ∞ A :=
    (EnergyBridge.contDiff_principalCoefficient S.g1 S.g1_admissible).comp (contDiff_const_smul lam)
  have hBc : ContDiff ℝ ∞ B :=
    (EnergyBridge.contDiff_principalCoefficient S.g2 S.g2_admissible).comp (contDiff_const_smul lam)
  have hAp : ∀ x ∈ U, (A x).PosDef := fun x _ =>
    EnergyBridge.principalCoefficient_posDef S.g1 S.g1_admissible (lam • x)
  have hBp : ∀ y ∈ V, (B y).PosDef := fun y _ =>
    EnergyBridge.principalCoefficient_posDef S.g2 S.g2_admissible (lam • y)
  have slice1 : ∀ {K : R3 × R3 → ℝ}, ContDiffOn ℝ ∞ K (U ×ˢ V) → ∀ y ∈ V,
      ContDiffOn ℝ ∞ (fun x => K (x, y)) U := fun hK y hy =>
    hK.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun x hx => Set.mk_mem_prod hx hy)
  have slice2 : ∀ {K : R3 × R3 → ℝ}, ContDiffOn ℝ ∞ K (U ×ˢ V) → ∀ x ∈ U,
      ContDiffOn ℝ ∞ (fun y => K (x, y)) V := fun hK x hx =>
    hK.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y hy => Set.mk_mem_prod hx hy)
  have first : ∀ {K : R3 × R3 → ℝ}, ProductSolutionOn S L lam K (U ×ˢ V) → ∀ y ∈ V, ∀ x ∈ U,
      divCoeffGrad A (fun z => K (z, y)) x = 0 := by
    intro K hK y hy x hx
    have h := hK.2.1 (x, y) (Set.mk_mem_prod hx hy)
    rw [coordinateFluxDivergence_metricDivergenceFlux_eq_Lop] at h
    exact h
  have second : ∀ {K : R3 × R3 → ℝ}, ProductSolutionOn S L lam K (U ×ˢ V) → ∀ x ∈ U, ∀ y ∈ V,
      divCoeffGrad B (fun z => K (x, z)) y = 0 := by
    intro K hK x hx y hy
    exact (normalizedSecondLaplacian_eq_zero_iff S.g1 S.g2 S.g1_admissible S.g2_admissible L lam
      _ y).mp (hK.2.2 (x, y) (Set.mk_mem_prod hx hy))
  have hH := eq_zero_on_product_of_separately_divCoeffGrad_eq_zero U V hU hUc hV hVc A B
    hAc.contDiffOn hAp hBc.contDiffOn hBp (fun x y => F (x, y) - G (x, y))
    (fun y hy => (slice1 hF.1 y hy).sub (slice1 hG.1 y hy))
    (fun y hy x hx => divCoeffGrad_sub_eq_zero (hAc.differentiable (by simp) x)
      (((slice1 hF.1 y hy).contDiffAt (hU.mem_nhds hx)).of_le (by simp))
      (((slice1 hG.1 y hy).contDiffAt (hU.mem_nhds hx)).of_le (by simp))
      (first hF y hy x hx) (first hG y hy x hx))
    (fun x hx => (slice2 hF.1 x hx).sub (slice2 hG.1 x hx))
    (fun x hx y hy => divCoeffGrad_sub_eq_zero (hBc.differentiable (by simp) y)
      (((slice2 hF.1 x hx).contDiffAt (hV.mem_nhds hy)).of_le (by simp))
      (((slice2 hG.1 x hx).contDiffAt (hV.mem_nhds hy)).of_le (by simp))
      (second hF x hx y hy) (second hG x hx y hy))
    U0 V0 hU0 hU0n hU0U hV0 hV0n hV0V (fun x hx y hy => by rw [hEq x hx y hy, sub_self])
  intro x hx y hy
  exact sub_eq_zero.mp (hH x hx y hy)

/-- LCT0: the original product-solution predicate restricts to subsets. -/
theorem productSolutionOn_mono {S : KnownSideSourceData} {L lam : ℝ} {F : R3 × R3 → ℝ}
    {U U' : Set (R3 × R3)} (h : ProductSolutionOn S L lam F U) (hU' : U' ⊆ U) :
    ProductSolutionOn S L lam F U' :=
  ⟨h.1.mono hU', fun v hv => h.2.1 v (hU' hv), fun v hv => h.2.2 v (hU' hv)⟩

/-- LCT: a native product solution on a connected box inside the initial cross that agrees with
the initial kernel on a nonempty open sub-box is the initial kernel there, and therefore satisfies
both ORIGINAL lower-cross identities on the box. -/
theorem eq_initialKernel_of_box (S : KnownSideSourceData) (L lam : ℝ) (hlam : 0 < lam)
    {U V U0 V0 : Set R3} (hU : IsOpen U) (hUc : IsConnected U)
    (hV : IsOpen V) (hVc : IsConnected V) (hbox : U ×ˢ V ⊆ initialCross S lam)
    {K : R3 × R3 → ℝ} (hK : ProductSolutionOn S L lam K (U ×ˢ V))
    (hU0 : IsOpen U0) (hU0n : U0.Nonempty) (hU0U : U0 ⊆ U)
    (hV0 : IsOpen V0) (hV0n : V0.Nonempty) (hV0V : V0 ⊆ V)
    (hEq : ∀ x ∈ U0, ∀ y ∈ V0, K (x, y) = initialKernel S lam (x, y)) :
    ∀ x ∈ U, ∀ y ∈ V, K (x, y) = initialKernel S lam (x, y) ∧
      (lam • y ∈ S.W → K (x, y) = dilatedKernel1 S lam (x, y)) ∧
      (lam • x ∈ S.W → K (x, y) = dilatedKernel2 S lam (x, y)) := by
  obtain ⟨-, hI, h1, h2⟩ := known_side_initial_cross_product S L lam hlam
  have hEqK := native_product_eq_of_eq_on_box S L lam hU hUc hV hVc hK
    (productSolutionOn_mono hI hbox) hU0 hU0n hU0U hV0 hV0n hV0V hEq
  intro x hx y hy
  have hxy := hEqK x hx y hy
  have hmem : (x, y) ∈ initialCross S lam := hbox (Set.mk_mem_prod hx hy)
  exact ⟨hxy, fun hW => hxy.trans (h1 (x, y) hmem hW),
    fun hW => hxy.trans (h2 (x, y) hmem hW)⟩

end NativeProductUCP

section SpherePole

/-- PE0: the SAME packet flow sends zero normal velocity to its centre (`hValue`). -/
theorem packetEndpoint_zero (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) {y : R3} (hy : y ∈ P.centers) (r : ℝ) :
    packetEndpoint S L P lam y r 0 = y := by
  obtain ⟨-, -, -, -, -, -, -, -, hValue, -, -⟩ := P.native_data.1.1.1
  unfold packetEndpoint referenceFramedPhysicalEndpoint
  simp only [map_zero, smul_zero]
  exact hValue lam hlam y (P.centers_room y hy).2

/-- PE1: a unit-sphere endpoint of positive admissible radius is never the pole. -/
theorem packetEndpoint_sphere_ne (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) cover.dilationCeiling)
    {y : R3} (hy : y ∈ (cover.packet i).centers) {r : ℝ} (hr0 : 0 < r)
    (hr : r < cover.radiusCeiling) {z : R3} (hz : z ∈ Metric.sphere (0 : R3) 1) :
    packetEndpoint S L (cover.packet i) lam y r z ≠ y := by
  intro h
  have h0 := packetEndpoint_zero S L (cover.packet i)
    ⟨hlam.1, hlam.2.trans cover.dilation_le_one⟩ hy r
  have hz1 : ‖z‖ = 1 := by
    rw [mem_sphere, dist_zero_right] at hz
    exact hz
  have hz2 : z ∈ Metric.closedBall (0 : R3) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have h02 : (0 : R3) ∈ Metric.closedBall (0 : R3) 2 :=
    Metric.mem_closedBall_self (by norm_num)
  have hz0 : z = 0 := cover.normal_injective i lam hlam y hy r hr0 hr hz2 h02 (h.trans h0.symm)
  rw [hz0, norm_zero] at hz1
  norm_num at hz1

/-- PE2: one dilation threshold, from `S` only, putting the whole scaled cylinder in the room. -/
theorem exists_cylinder_room (S : KnownSideSourceData) :
    ∃ lamC : ℝ, 0 < lamC ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lamC →
      ∀ y ∈ cylinder, lam • y ∈ S.coordinateRoom := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp S.coordinateRoom_open 0 S.origin_mem
  refine ⟨r / 4, by positivity, fun lam hlam hlamC y hy => hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
  have h2 := cylinder_norm_le hy
  have h3 : lam * ‖y‖ ≤ lam * 2 := mul_le_mul_of_nonneg_left h2 hlam.le
  linarith

/-- PE3: every sphere-cover pair of the endpoint lies in the dilated off-diagonal room. -/
theorem sphere_pair_mem_dilatedOffDiagonal (S : KnownSideSourceData) (L : ℝ)
    (cover : NativeNormalCover S L) (i : Fin cover.count) {lam : ℝ}
    (hlam : lam ∈ Set.Icc (0 : ℝ) cover.dilationCeiling) {y : R3}
    (hy : y ∈ (cover.packet i).centers) (hyroom : lam • y ∈ S.coordinateRoom) {r : ℝ}
    (hr0 : 0 < r) (hr : r < cover.radiusCeiling) {z : R3} (hz : z ∈ Metric.sphere (0 : R3) 1) :
    (packetEndpoint S L (cover.packet i) lam y r z, y) ∈ dilatedOffDiagonal S lam := by
  have hz2 : z ∈ Metric.closedBall (0 : R3) 2 := by
    rw [mem_sphere, dist_zero_right] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  exact ⟨cover.coordinate_room i lam hlam y hy r hr0 hr z hz2, hyroom,
    packetEndpoint_sphere_ne S L cover i hlam hy hr0 hr hz⟩

/-- RC: one `R0` (from `L, p, c`) bounding the actual reference radius below `c` on the whole
cylinder, for every `Rstar ≤ R0` and every `δ ∈ (0,1]`. -/
theorem exists_referenceRadius_ceiling (L : ℝ) (p : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ Rstar : ℝ, 0 < Rstar → Rstar ≤ R0 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ y ∈ cylinder, referenceRadius δ Rstar p L y < c := by
  obtain ⟨T, hT⟩ := (isCompact_closedBall (0 : R3) 2).bddAbove_image
    (ConformalDepth.contDiff_referenceDepth L).continuous.continuousOn
  have hM0 : 0 < Real.log (1 + Real.exp T) := RadiusProfile.log_exp_add_one_pos T
  have hMp : 0 < Real.log (1 + Real.exp T) ^ p := pow_pos hM0 p
  refine ⟨c / (2 * Real.log (1 + Real.exp T) ^ p), by positivity,
    fun Rstar hR hRle δ hδ hδ1 y hy => ?_⟩
  have hyB : y ∈ Metric.closedBall (0 : R3) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact cylinder_norm_le hy
  have hdT : ConformalDepth.referenceDepth L y ≤ T := hT ⟨y, hyB, rfl⟩
  have hs : RadiusProfile.softplus δ (ConformalDepth.referenceDepth L y) ≤
      Real.log (1 + Real.exp T) :=
    RadiusProfile.softplus_le_log_exp_upper δ _ T hδ hδ1 hdT
  have hs0 : 0 < RadiusProfile.softplus δ (ConformalDepth.referenceDepth L y) :=
    RadiusProfile.softplus_pos δ _ hδ
  have hpow : RadiusProfile.softplus δ (ConformalDepth.referenceDepth L y) ^ p ≤
      Real.log (1 + Real.exp T) ^ p := pow_le_pow_left₀ hs0.le hs p
  unfold referenceRadius
  calc Rstar * RadiusProfile.softplus δ (ConformalDepth.referenceDepth L y) ^ p
      ≤ Rstar * Real.log (1 + Real.exp T) ^ p := mul_le_mul_of_nonneg_left hpow hR.le
    _ ≤ c / (2 * Real.log (1 + Real.exp T) ^ p) * Real.log (1 + Real.exp T) ^ p :=
        mul_le_mul_of_nonneg_right hRle hMp.le
    _ = c / 2 := by
        rw [div_mul_eq_mul_div, mul_comm (2 : ℝ) (Real.log (1 + Real.exp T) ^ p), ← div_div,
          mul_div_assoc, div_self hMp.ne', mul_one]
    _ < c := by linarith

end SpherePole

section BasisArm
open scoped ENNReal Matrix.Norms.Elementwise

/-- BA1: the exported room interpolation, applied to the SAME harmonic class and its smooth
representative, bounds the inner restriction by the observed restriction. -/
theorem harmonic_basis_interp_bound (D O Sv : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (hA : ContDiffOn ℝ ∞ A D)
    (hpos : ∀ x ∈ D, (A x).PosDef) (hOD : O ⊆ D) (hSD : Sv ⊆ D) {Kint γ : ℝ}
    (hI : ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict D)) (q : R3 → ℝ),
      q =ᵐ[(volume : Measure R3).restrict D] (u : R3 → ℝ) → ContDiffOn ℝ ∞ q D →
      (∀ x ∈ D, divCoeffGrad A q x = 0) →
      ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict O))
        (uS : Lp ℝ 2 ((volume : Measure R3).restrict Sv)),
      q =ᵐ[(volume : Measure R3).restrict O] (uO : R3 → ℝ) →
      q =ᵐ[(volume : Measure R3).restrict Sv] (uS : R3 → ℝ) →
      ‖uO‖ ≤ Kint * (‖uS‖ ^ γ * ‖u‖ ^ (1 - γ)))
    (w : harmonicSub D hD A hA) (hw : ‖w‖ = 1) :
    ‖harmonicRestrict D hD A hA O hOD w‖ ≤ Kint * ‖harmonicRestrict D hD A hA Sv hSD w‖ ^ γ := by
  obtain ⟨hc, hae, hP⟩ := harmonicRep_spec D hD A hA hpos w
  have hrestr : ∀ (T : Set R3) (hTD : T ⊆ D),
      harmonicRep D hD A hA hpos w =ᵐ[(volume : Measure R3).restrict T]
        (harmonicRestrict D hD A hA T hTD w : R3 → ℝ) := by
    intro T hTD
    have h1 : harmonicRep D hD A hA hpos w =ᵐ[(volume : Measure R3).restrict T]
        ((w : Lp ℝ 2 ((volume : Measure R3).restrict D)) : R3 → ℝ) :=
      ae_restrict_of_ae_restrict_of_subset hTD hae
    have h2 : (harmonicRestrict D hD A hA T hTD w : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict T]
        ((w : Lp ℝ 2 ((volume : Measure R3).restrict D)) : R3 → ℝ) :=
      Lp.coeFn_LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤)
        (by simpa only [one_smul] using Measure.restrict_mono_set volume hTD) _
    exact h1.trans h2.symm
  have h := hI (w : Lp ℝ 2 ((volume : Measure R3).restrict D)) _ hae hc hP _ _
    (hrestr O hOD) (hrestr Sv hSD)
  have hn : ‖(w : Lp ℝ 2 ((volume : Measure R3).restrict D))‖ = 1 := by
    rw [← hw]
    rfl
  rw [hn, Real.one_rpow, mul_one] at h
  exact h

/-- BA2: on the SAME spectral system, `‖R_O wᵢ‖ ≤ Kint μᵢ^γ` (source: `‖w_j‖_{L²(O₁)} ≤ Cμ_j^{γ₁}`). -/
theorem harmonic_basis_interp_bound_spectral (D O Sv : Set R3) (hD : IsOpen D)
    (A : R3 → Matrix (Fin 3) (Fin 3) ℝ) (hA : ContDiffOn ℝ ∞ A D)
    (hpos : ∀ x ∈ D, (A x).PosDef) (hOD : O ⊆ D) (hSD : Sv ⊆ D) {Kint γ : ℝ}
    (hI : ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict D)) (q : R3 → ℝ),
      q =ᵐ[(volume : Measure R3).restrict D] (u : R3 → ℝ) → ContDiffOn ℝ ∞ q D →
      (∀ x ∈ D, divCoeffGrad A q x = 0) →
      ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict O))
        (uS : Lp ℝ 2 ((volume : Measure R3).restrict Sv)),
      q =ᵐ[(volume : Measure R3).restrict O] (uO : R3 → ℝ) →
      q =ᵐ[(volume : Measure R3).restrict Sv] (uS : R3 → ℝ) →
      ‖uO‖ ≤ Kint * (‖uS‖ ^ γ * ‖u‖ ^ (1 - γ)))
    {ι : Type*} (w : HilbertBasis ι ℝ (harmonicSub D hD A hA)) (μ : ι → ℝ)
    (hμ : ∀ i, 0 < μ i)
    (hgram : ∀ i j, inner ℝ (harmonicRestrict D hD A hA Sv hSD (w i))
      (harmonicRestrict D hD A hA Sv hSD (w j)) = if i = j then μ i ^ 2 else 0) (i : ι) :
    ‖harmonicRestrict D hD A hA O hOD (w i)‖ ≤ Kint * μ i ^ γ := by
  have hb := harmonic_basis_interp_bound D O Sv hD A hA hpos hOD hSD hI (w i)
    (w.orthonormal.1 i)
  have hsq : ‖harmonicRestrict D hD A hA Sv hSD (w i)‖ ^ 2 = μ i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hgram, if_pos rfl]
  have heq : ‖harmonicRestrict D hD A hA Sv hSD (w i)‖ = μ i :=
    (sq_eq_sq₀ (norm_nonneg _) (hμ i).le).mp hsq
  rwa [heq] at hb

end BasisArm

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
