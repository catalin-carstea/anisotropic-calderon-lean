import Calderon.ClassicalHarmonicL2Space
import Calderon.LocalMetricGeodesicEndpoint
import Calderon.MixedKernelConstruction.TaskInterface
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask.Geometry
open Set Metric Filter
open scoped ContDiff Topology
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

theorem coordinateOffDiagonal_isOpen (S : KnownSideSourceData) :
    IsOpen (coordinateOffDiagonal S) := by
  have h1 : IsOpen {v : R3 × R3 | v.1 ∈ S.coordinateRoom} :=
    S.coordinateRoom_open.preimage continuous_fst
  have h2 : IsOpen {v : R3 × R3 | v.2 ∈ S.coordinateRoom} :=
    S.coordinateRoom_open.preimage continuous_snd
  have h3 : IsOpen {v : R3 × R3 | v.1 ≠ v.2} :=
    isOpen_ne_fun continuous_fst continuous_snd
  exact h1.inter (h2.inter h3)

/-- Transport of the SAME-kernel joint theorem through one actual
branch. The input kernel class is the separately smooth one; its first
conjunct is the symmetric inverse-source predicate used by the theorem. -/
theorem branchKernel_contDiffOn (S : KnownSideSourceData) (g : MatrixField)
    (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSeparatelySmoothInverseSourceKernel g hg K G)
    (Xi : R3 → R3) (hXi : ContDiffOn ℝ ∞ Xi S.coordinateRoom)
    (hinj : Set.InjOn Xi S.coordinateRoom)
    (hroom : ∀ x ∈ S.coordinateRoom, Xi x ∈ (radiusTwoOpens : Set R3)) :
    ContDiffOn ℝ ∞ (fun v : R3 × R3 =>
      if hy : v.2 ∈ S.coordinateRoom then G ⟨Xi v.2, hroom v.2 hy⟩ (Xi v.1) else 0)
      (coordinateOffDiagonal S) := by
  intro v hv
  obtain ⟨h1, h2, hne⟩ := hv
  let J : R3 × R3 → ℝ := fun w =>
    if hp : w.1 ∈ (radiusTwoOpens : Set R3) then G ⟨w.1, hp⟩ w.2 else 0
  have hJ : ContDiffAt ℝ ∞ J (Xi v.2, Xi v.1) :=
    contDiffAt_radiusTwo_sourceKernel_offDiagonal S.hreg S.hcalc g hg K G hData.1
      ⟨Xi v.2, hroom _ h2⟩ ⟨Xi v.1, hroom _ h1⟩ (fun h => hne (hinj h1 h2 h.symm))
  have hXiAt : ∀ x ∈ S.coordinateRoom, ContDiffAt ℝ ∞ Xi x := fun x hx =>
    hXi.contDiffAt (S.coordinateRoom_open.mem_nhds hx)
  have hmap : ContDiffAt ℝ ∞ (fun w : R3 × R3 => (Xi w.2, Xi w.1)) v :=
    ((hXiAt _ h2).comp v contDiffAt_snd).prodMk ((hXiAt _ h1).comp v contDiffAt_fst)
  have hcomp : ContDiffAt ℝ ∞ (J ∘ fun w : R3 × R3 => (Xi w.2, Xi w.1)) v :=
    hJ.comp v hmap
  have heq : (fun v : R3 × R3 =>
      if hy : v.2 ∈ S.coordinateRoom then G ⟨Xi v.2, hroom v.2 hy⟩ (Xi v.1) else 0)
      =ᶠ[𝓝 v] (J ∘ fun w : R3 × R3 => (Xi w.2, Xi w.1)) := by
    filter_upwards [(S.coordinateRoom_open.preimage continuous_snd).mem_nhds h2]
      with w hw
    have hw' : w.2 ∈ S.coordinateRoom := hw
    show _ = J (Xi w.2, Xi w.1)
    simp only [J, dif_pos hw', dif_pos (hroom _ hw')]
  exact (hcomp.congr_of_eventuallyEq heq).contDiffWithinAt

/-- Derived SAME-original-kernel jointness; no stronger input kernel class. -/
theorem original_kernel_joint_regular : OriginalKernelJointRegularityGoal := by
  intro S
  exact ⟨branchKernel_contDiffOn S S.original1 S.original1_admissible S.K1 S.G1
      S.kernel1 S.Xi1 S.Xi1_smooth S.Xi1_injective S.Xi1_room,
    branchKernel_contDiffOn S S.original2 S.original2_admissible S.K2 S.G2
      S.kernel2 S.Xi2 S.Xi2_smooth S.Xi2_injective S.Xi2_room⟩

theorem initialCross_isOpen (S : KnownSideSourceData) (lam : ℝ) :
    IsOpen (initialCross S lam) := by
  have hs : Continuous fun v : R3 × R3 => lam • v.1 := continuous_fst.const_smul lam
  have ht : Continuous fun v : R3 × R3 => lam • v.2 := continuous_snd.const_smul lam
  have h1 : IsOpen {v : R3 × R3 | lam • v.1 ∈ S.coordinateRoom} :=
    S.coordinateRoom_open.preimage hs
  have h2 : IsOpen {v : R3 × R3 | lam • v.2 ∈ S.coordinateRoom} :=
    S.coordinateRoom_open.preimage ht
  have h3 : IsOpen {v : R3 × R3 | v.1 ≠ v.2} :=
    isOpen_ne_fun continuous_fst continuous_snd
  have h4 : IsOpen {v : R3 × R3 | lam • v.1 ∈ S.W ∨ lam • v.2 ∈ S.W} :=
    (S.W_open.preimage hs).union (S.W_open.preimage ht)
  exact (h1.inter (h2.inter h3)).inter h4

/-- Joint smoothness of the dilated SAME-original kernels off the dilated diagonal. -/
theorem dilatedKernel1_contDiffOn (S : KnownSideSourceData) (lam : ℝ) (hlam : 0 < lam) :
    ContDiffOn ℝ ∞ (dilatedKernel1 S lam) (dilatedOffDiagonal S lam) := by
  have hJ := (original_kernel_joint_regular S).1
  have hmap : ContDiff ℝ ∞ (fun v : R3 × R3 => (lam • v.1, lam • v.2)) :=
    (contDiff_fst.const_smul lam).prodMk (contDiff_snd.const_smul lam)
  have hmaps : MapsTo (fun v : R3 × R3 => (lam • v.1, lam • v.2))
      (dilatedOffDiagonal S lam) (coordinateOffDiagonal S) := by
    rintro v ⟨h1, h2, hne⟩
    refine ⟨h1, h2, fun h => hne ?_⟩
    exact smul_right_injective R3 hlam.ne' h
  exact contDiffOn_const.mul (hJ.comp hmap.contDiffOn hmaps)

theorem dilatedKernel2_contDiffOn (S : KnownSideSourceData) (lam : ℝ) (hlam : 0 < lam) :
    ContDiffOn ℝ ∞ (dilatedKernel2 S lam) (dilatedOffDiagonal S lam) := by
  have hJ := (original_kernel_joint_regular S).2
  have hmap : ContDiff ℝ ∞ (fun v : R3 × R3 => (lam • v.1, lam • v.2)) :=
    (contDiff_fst.const_smul lam).prodMk (contDiff_snd.const_smul lam)
  have hmaps : MapsTo (fun v : R3 × R3 => (lam • v.1, lam • v.2))
      (dilatedOffDiagonal S lam) (coordinateOffDiagonal S) := by
    rintro v ⟨h1, h2, hne⟩
    refine ⟨h1, h2, fun h => hne ?_⟩
    exact smul_right_injective R3 hlam.ne' h
  exact contDiffOn_const.mul (hJ.comp hmap.contDiffOn hmaps)

/-- The SAME-original-kernel overlap identity after the dilation. -/
theorem dilatedKernel_overlap (S : KnownSideSourceData) (lam : ℝ) (hlam : 0 < lam)
    (v : R3 × R3) (hv : v ∈ dilatedOffDiagonal S lam)
    (h1 : lam • v.1 ∈ S.W) (h2 : lam • v.2 ∈ S.W) :
    dilatedKernel1 S lam v = dilatedKernel2 S lam v := by
  obtain ⟨-, hr2, hne⟩ := hv
  have hne' : lam • v.1 ≠ lam • v.2 := fun h => hne (smul_right_injective R3 hlam.ne' h)
  have hm := S.kernels_match (lam • v.1) h1 (lam • v.2) h2 hne'
  simp only [dilatedKernel1, dilatedKernel2, coordinateKernel1, coordinateKernel2,
    dif_pos hr2]
  rw [hm]

theorem initialKernel_eq_dilatedKernel1 (S : KnownSideSourceData) (lam : ℝ)
    (v : R3 × R3) (h2 : lam • v.2 ∈ S.W) :
    initialKernel S lam v = dilatedKernel1 S lam v := by
  simp only [initialKernel, if_pos h2]

theorem initialKernel_eq_dilatedKernel2 (S : KnownSideSourceData) (lam : ℝ)
    (hlam : 0 < lam) (v : R3 × R3) (hv : v ∈ dilatedOffDiagonal S lam)
    (h1 : lam • v.1 ∈ S.W) :
    initialKernel S lam v = dilatedKernel2 S lam v := by
  by_cases h2 : lam • v.2 ∈ S.W
  · rw [initialKernel_eq_dilatedKernel1 S lam v h2]
    exact dilatedKernel_overlap S lam hlam v hv h1 h2
  · simp only [initialKernel, if_neg h2]

theorem initialKernel_contDiffOn (S : KnownSideSourceData) (lam : ℝ) (hlam : 0 < lam) :
    ContDiffOn ℝ ∞ (initialKernel S lam) (initialCross S lam) := by
  intro v hv
  have hopen := initialCross_isOpen S lam
  refine ContDiffAt.contDiffWithinAt ?_
  have hvOff : v ∈ dilatedOffDiagonal S lam := hv.1
  have hOffOpen : IsOpen (dilatedOffDiagonal S lam) := by
    have hs : Continuous fun v : R3 × R3 => lam • v.1 := continuous_fst.const_smul lam
    have ht : Continuous fun v : R3 × R3 => lam • v.2 := continuous_snd.const_smul lam
    exact (S.coordinateRoom_open.preimage hs).inter
      ((S.coordinateRoom_open.preimage ht).inter
        (isOpen_ne_fun continuous_fst continuous_snd))
  rcases hv.2 with h1 | h2
  · have hU : IsOpen (dilatedOffDiagonal S lam ∩ {w : R3 × R3 | lam • w.1 ∈ S.W}) :=
      hOffOpen.inter (S.W_open.preimage (continuous_fst.const_smul lam))
    have hd : ContDiffAt ℝ ∞ (dilatedKernel2 S lam) v :=
      (dilatedKernel2_contDiffOn S lam hlam).contDiffAt (hOffOpen.mem_nhds hvOff)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds ⟨hvOff, h1⟩] with w hw
    exact initialKernel_eq_dilatedKernel2 S lam hlam w hw.1 hw.2
  · have hU : IsOpen {w : R3 × R3 | lam • w.2 ∈ S.W} :=
      S.W_open.preimage (continuous_snd.const_smul lam)
    have hd : ContDiffAt ℝ ∞ (dilatedKernel1 S lam) v :=
      (dilatedKernel1_contDiffOn S lam hlam).contDiffAt (hOffOpen.mem_nhds hvOff)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds h2] with w hw
    exact initialKernel_eq_dilatedKernel1 S lam w hw

/-! ## C1b: finite same-flow normal cover (Steps 0–6) -/

/-- Step 1: the actual geodesic phase field of each parameter slice is smooth. -/
theorem contDiff_conformalReference_geodesicPhaseField (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L q : ℝ) :
    ContDiff ℝ ∞ (geodesicPhaseField
      (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
      (metricOperatorField (conformalReferenceMatrix g L q))) := by
  have hslice : ContDiff ℝ ∞ (fun y : R3 => (q, y)) := contDiff_const.prodMk contDiff_id
  have hQ : ContDiff ℝ ∞ (fun y : R3 =>
      Ring.inverse (conformalReferenceOperatorJoint g L (q, y))) :=
    (contDiff_conformalReferenceInverseJoint g hg L).comp hslice
  have hM : ContDiff ℝ ∞ (fun y : R3 => conformalReferenceOperatorJoint g L (q, y)) :=
    (contDiff_conformalReferenceOperatorJoint g hg L).comp hslice
  exact contDiff_geodesicPhaseField _ _ hQ hM

/-- Step 2: uniqueness for an autonomous `C^1` field on `[0,1]`. -/
theorem flow_eq_one_of_same_ODE (V : R3 × R3 → R3 × R3) (hV : ContDiff ℝ 1 V)
    (f h : ℝ → R3 × R3)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (V (f t)) t)
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt h (V (h t)) t)
    (h0 : f 0 = h 0) : f 1 = h 1 := by
  have hfc : ContinuousOn f (Icc (0 : ℝ) 1) := fun t ht =>
    (hf t ht).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (Icc (0 : ℝ) 1) := fun t ht =>
    (hh t ht).continuousAt.continuousWithinAt
  obtain ⟨R, hR⟩ := ((isCompact_Icc.image_of_continuousOn hfc).union
    (isCompact_Icc.image_of_continuousOn hhc)).isBounded.subset_closedBall 0
  obtain ⟨K, hK⟩ := (hV.contDiffOn (s := closedBall (0 : R3 × R3) R)).exists_lipschitzOnWith
    one_ne_zero (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hEq := ODE_solution_unique_of_mem_Icc_right (v := fun _ => V)
    (s := fun _ => closedBall (0 : R3 × R3) R) (K := K) (a := 0) (b := 1)
    (fun _ _ => hK) hfc
    (fun t ht => (hf t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => hR (Or.inl (mem_image_of_mem f (Ico_subset_Icc_self ht))))
    hhc (fun t ht => (hh t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => hR (Or.inr (mem_image_of_mem h (Ico_subset_Icc_self ht)))) h0
  exact hEq ⟨zero_le_one, le_rfl⟩

/-- Step 0 (read-off): the packet's own endpoint data and its retained room. -/
theorem packet_room (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B ∧
    ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y - P.y0‖ ≤ 4 * P.rho → ∀ r : ℝ, |r| ≤ 4 * P.rho →
      ∀ z ∈ closedBall (0 : R3) 2,
        (y, r • conformalReferenceGramFrameOperatorJoint S.g1 L (q, y) z) ∈ P.B ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          HasDerivAt (P.Phi q (y, r • conformalReferenceGramFrameOperatorJoint S.g1 L (q, y) z))
            (geodesicPhaseField
              (inverseMetricField (metricOperatorField (conformalReferenceMatrix S.g1 L q)))
              (metricOperatorField (conformalReferenceMatrix S.g1 L q))
              (P.Phi q (y, r • conformalReferenceGramFrameOperatorJoint S.g1 L (q, y) z) t)) t := by
  obtain ⟨hPos, -⟩ := P.native_data
  obtain ⟨hNormal, -, hρε, -⟩ := hPos
  obtain ⟨hEnd, -, -, -, -, -, hroom, -⟩ := hNormal
  refine ⟨hEnd, fun q hq y hy r hr z hz => ?_⟩
  obtain ⟨hB, hODE, -⟩ := hroom q hq y (hy.trans hρε) r (hr.trans hρε) z hz
  exact ⟨hB, hODE⟩

/-- Step 3: overlap coherence of two packets' endpoints, by actual ODE uniqueness. -/
theorem packet_endpoint_coherence (S : KnownSideSourceData) (L : ℝ)
    (P P' : NativeNormalPacket S L) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3)
    (hy : ‖y - P.y0‖ ≤ 4 * P.rho) (hy' : ‖y - P'.y0‖ ≤ 4 * P'.rho)
    (r : ℝ) (hr : |r| ≤ 4 * P.rho) (hr' : |r| ≤ 4 * P'.rho)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    packetEndpoint S L P q y r z = packetEndpoint S L P' q y r z := by
  obtain ⟨hE, hR⟩ := packet_room S L P
  obtain ⟨hE', hR'⟩ := packet_room S L P'
  obtain ⟨-, -, -, hinit, -⟩ := hE
  obtain ⟨-, -, -, hinit', -⟩ := hE'
  set x : R3 × R3 := (y, r • conformalReferenceGramFrameOperatorJoint S.g1 L (q, y) z)
  have hV : ContDiff ℝ 1 (geodesicPhaseField
      (inverseMetricField (metricOperatorField (conformalReferenceMatrix S.g1 L q)))
      (metricOperatorField (conformalReferenceMatrix S.g1 L q))) :=
    (contDiff_conformalReference_geodesicPhaseField S.g1 S.g1_admissible L q).of_le
      (by simp)
  have h1 := flow_eq_one_of_same_ODE _ hV (P.Phi q x) (P'.Phi q x)
    (hR q hq y hy r hr z hz).2 (hR' q hq y hy' r hr' z hz).2
    (by rw [hinit q x, hinit' q x])
  show (P.Phi q x 1).1 = (P'.Phi q x 1).1
  rw [h1]

/-- Step 4: a same-flow injectivity radius for one packet. -/
theorem packet_exists_injective_radius (S : KnownSideSourceData) (L : ℝ)
    (Pk : NativeNormalPacket S L) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ c : R3, ‖c - Pk.y0‖ ≤ 4 * Pk.rho →
      ∀ r : ℝ, 0 < r → r ≤ δ →
        InjOn (packetEndpoint S L Pk q c r) (closedBall (0 : R3) 2) := by
  have hg := S.g1_admissible
  obtain ⟨hE, hR⟩ := packet_room S L Pk
  obtain ⟨-, -, -, -, -, -, -, hΘ, hvalue, hfirst, -⟩ := hE
  have hε : 0 < 4 * Pk.rho := by linarith [Pk.rho_positive]
  have hcB (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (c : R3) (hc : ‖c - Pk.y0‖ ≤ 4 * Pk.rho) :
      (c, 0) ∈ Pk.B := by
    have h := (hR q hq c hc 0 (by rw [abs_zero]; exact hε.le) 0
      (mem_closedBall_self (by norm_num))).1
    simpa only [zero_smul] using h
  have hQzero : ∀ q ∈ Icc (0 : ℝ) 1, ∀ c, ‖c - Pk.y0‖ ≤ 4 * Pk.rho →
      ∀ z ∈ closedBall (0 : R3) 2,
        referenceWhitenedEndpointJacobian S.g1 L Pk.Phi (q, ((c, 0), z)) =
          ContinuousLinearMap.id ℝ R3 := by
    intro q hq c hc z _
    unfold referenceWhitenedEndpointJacobian referenceGramFrameInverse
    rw [referenceFramedNormalizedJacobian_zero S.g1 L Pk.Phi q c z
      (hfirst q hq c (hcB q hq c hc))]
    exact (referenceGramFrame_isInvertible S.g1 hg L (q, c)).inverse_comp_self
  obtain ⟨δ, hδ, -, hbound⟩ := exists_signed_radius_of_compact_identity_slice
    (referenceWhitenedEndpointJacobian S.g1 L Pk.Phi)
    (contDiff_referenceWhitenedEndpointJacobian S.g1 hg L Pk.Phi hΘ).continuous
    Pk.y0 (4 * Pk.rho) hε hQzero
  refine ⟨δ, hδ, fun q hq c hc r hr hrδ => ?_⟩
  have hrabs : |r| ≤ δ := by rw [abs_of_pos hr]; exact hrδ
  have hfirstc := hfirst q hq c (hcB q hq c hc)
  have hΘq : ContDiff ℝ ∞ (fun a => (Pk.Phi q a 1).1) :=
    hΘ.comp (contDiff_const.prodMk contDiff_id)
  let E : R3 → R3 := fun z => referenceFramedNormalizedEndpoint S.g1 L Pk.Phi (q, ((c, r), z))
  let A : R3 →L[ℝ] R3 := referenceGramFrameInverse S.g1 L (q, c)
  let Q : R3 → R3 →L[ℝ] R3 := fun z =>
    referenceWhitenedEndpointJacobian S.g1 L Pk.Phi (q, ((c, r), z))
  have hEder (z : R3) : HasFDerivAt E
      (referenceFramedNormalizedJacobian S.g1 L Pk.Phi (q, ((c, r), z))) z :=
    hasFDerivAt_referenceFramedNormalizedEndpoint_slice S.g1 L Pk.Phi q c z r hΘq hfirstc
  have hWder (z : R3) : HasFDerivAt (fun w => A (E w)) (Q z) z :=
    (A.hasFDerivAt (x := E z)).comp z (hEder z)
  have hiE : InjOn E (closedBall (0 : R3) 2) := by
    intro x hx y hy hxy
    have h : (1/2 : ℝ) * ‖y - x‖ ≤ ‖A (E y) - A (E x)‖ :=
      norm_lower_bound_of_derivative_near_id_closedBall
        (fun w => A (E w)) Q (fun z _ => hWder z)
        (fun z hz => (hbound q hq c hc r hrabs z hz).le) x hx y hy
    rw [hxy, sub_self, norm_zero] at h
    have hz : ‖y - x‖ = 0 := by linarith [norm_nonneg (y - x)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  intro x hx y hy hxy
  apply hiE hx hy
  have hne : r ≠ 0 := hr.ne'
  show referenceFramedNormalizedEndpoint S.g1 L Pk.Phi (q, ((c, r), x)) =
    referenceFramedNormalizedEndpoint S.g1 L Pk.Phi (q, ((c, r), y))
  simp only [referenceFramedNormalizedEndpoint, hne, ite_false]
  exact congrArg (fun w : R3 => r⁻¹ • (w - c)) hxy

/-- Step 5: a uniform endpoint bound on the packet's compact room. -/
theorem packet_endpoint_bounded (S : KnownSideSourceData) (L : ℝ)
    (Pk : NativeNormalPacket S L) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ c : R3, ‖c - Pk.y0‖ ≤ 4 * Pk.rho →
      ∀ r : ℝ, |r| ≤ 4 * Pk.rho → ∀ z ∈ closedBall (0 : R3) 2,
        ‖packetEndpoint S L Pk q c r z‖ ≤ M := by
  obtain ⟨hE, -⟩ := packet_room S L Pk
  obtain ⟨-, -, -, -, -, -, -, hΘ, -⟩ := hE
  have hcont : Continuous (referenceFramedPhysicalEndpoint S.g1 L Pk.Phi) :=
    (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L Pk.Phi hΘ).continuous
  let K : Set ReferenceEndpointVariables :=
    Icc (0 : ℝ) 1 ×ˢ ((closedBall Pk.y0 (4 * Pk.rho) ×ˢ closedBall (0 : ℝ) (4 * Pk.rho)) ×ˢ
      closedBall (0 : R3) 2)
  have hK : IsCompact K := isCompact_Icc.prod
    (((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).prod (isCompact_closedBall _ _))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun q hq c hc r hr z hz => ?_⟩
  have hmem : (q, ((c, r), z)) ∈ K := by
    refine ⟨hq, ⟨⟨?_, ?_⟩, hz⟩⟩
    · rw [mem_closedBall, dist_eq_norm]; exact hc
    · rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]; exact hr
  exact (hC _ hmem).trans (le_max_left _ _)

/-- Step 0: one actual native packet whose center set contains the given center. -/
theorem exists_localPacket (S : KnownSideSourceData) (L : ℝ) (y0 : R3) :
    ∃ P : NativeNormalPacket S L, y0 ∈ P.centers := by
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
      rho_positive := hρ }, mem_ball_self hρ⟩
  intro y hy
  have hy' : ‖y - y0‖ < ρ := by rwa [mem_ball, dist_eq_norm] at hy
  refine ⟨by linarith, ?_⟩
  have h := (hroom 0 ⟨le_rfl, zero_le_one⟩ y (by linarith) 0
    (by rw [abs_zero]; linarith) 0 (mem_closedBall_self (by norm_num))).1
  simpa only [zero_smul] using h

theorem norm_le_two_of_mem_cylinder {y : R3} (hy : y ∈ cylinder) : ‖y‖ ≤ 2 := by
  obtain ⟨h01, h2l, h2u⟩ := hy
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  have h22 : y 2 ^ 2 ≤ 1 := by nlinarith
  rw [Real.sqrt_le_left (by norm_num)]
  nlinarith

theorem isCompact_cylinder : IsCompact cylinder := by
  have hc : ∀ i : Fin 3, Continuous fun y : R3 => y i := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
  have hclosed : IsClosed cylinder :=
    (isClosed_le (((hc 0).pow 2).add ((hc 1).pow 2)) continuous_const).inter
      ((isClosed_le continuous_const (hc 2)).inter (isClosed_le (hc 2) continuous_const))
  refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
  refine (Metric.isBounded_iff_subset_closedBall (0 : R3)).2 ⟨2, fun y hy => ?_⟩
  rw [mem_closedBall, dist_zero_right]
  exact norm_le_two_of_mem_cylinder hy

theorem exists_pos_le_finite {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ m : ℝ, 0 < m ∧ ∀ i, m ≤ f i := by
  induction n with
  | zero => exact ⟨1, one_pos, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨m, hm, h⟩ := ih (fun i => f i.succ) (fun i => hf _)
    refine ⟨min m (f 0), lt_min hm (hf 0), fun i => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h j)

/-- Construct finite LOCAL native normal packets covering the ENTIRE cylinder,
with explicit overlap coherence and positive common room. -/
theorem normal_packet_cover_exists : NativeNormalPacketCoverGoal := by
  intro S L _
  choose P hP using fun y : R3 => exists_localPacket S L y
  obtain ⟨t, ht⟩ := isCompact_cylinder.elim_finite_subcover (fun y : R3 => (P y).centers)
    (fun y => (P y).centers_open) (fun y _ => mem_iUnion.2 ⟨y, hP y⟩)
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
      endpoint_coherence := ?_ }⟩
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

theorem fderiv_smul_of_ne {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (hc : c ≠ 0) (f : R3 → E) (y : R3) :
    fderiv ℝ (fun z => c • f z) y = c • fderiv ℝ f y := by
  haveI := invertibleOfNonzero hc
  exact fderiv_const_smul_of_invertible c

theorem gradient_const_mul_of_ne (c : ℝ) (hc : c ≠ 0) (u : R3 → ℝ) (y : R3) :
    gradient (fun z => c * u z) y = c • gradient u y := by
  apply ext_inner_right ℝ
  intro V
  rw [inner_gradient_left, real_inner_smul_left, inner_gradient_left]
  have h := fderiv_smul_of_ne c hc u y
  simp only [smul_eq_mul] at h
  rw [h]
  rfl

theorem fluxDiv_const_mul (g : MatrixField) (u : R3 → ℝ) (x : R3) (c : ℝ) (hc : c ≠ 0) :
    coordinateFluxDivergence (metricDivergenceFlux g (fun z => c * u z)) x =
      c * coordinateFluxDivergence (metricDivergenceFlux g u) x := by
  have hF : metricDivergenceFlux g (fun z => c * u z) =
      fun y => c • metricDivergenceFlux g u y := by
    funext y
    simp only [metricDivergenceFlux, gradient_const_mul_of_ne c hc, map_smul]
  rw [hF]
  unfold coordinateFluxDivergence
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (fun y => (c • metricDivergenceFlux g u y) i) =
      fun y => c • (metricDivergenceFlux g u y i) := by
    funext y
    simp
  rw [hi, fderiv_smul_of_ne c hc]
  rfl

theorem fluxDiv_congr_metric (g g' : MatrixField) (u : R3 → ℝ) (x : R3)
    (h : g =ᶠ[𝓝 x] g') :
    coordinateFluxDivergence (metricDivergenceFlux g u) x =
      coordinateFluxDivergence (metricDivergenceFlux g' u) x := by
  have hF : metricDivergenceFlux g u =ᶠ[𝓝 x] metricDivergenceFlux g' u := by
    filter_upwards [h] with y hy
    have hP : principalCoefficient g y = principalCoefficient g' y := by
      show Real.sqrt (g y).det • (g y)⁻¹ = Real.sqrt (g' y).det • (g' y)⁻¹
      rw [hy]
    simp only [metricDivergenceFlux, hP]
  unfold coordinateFluxDivergence
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (fun y => metricDivergenceFlux g u y i) =ᶠ[𝓝 x]
      (fun y => metricDivergenceFlux g' u y i) := by
    filter_upwards [hF] with y hy
    rw [hy]
  rw [hi.fderiv_eq]

/-- The native normalized second operator is a scalar multiple of the exact
flux divergence for the dilated second metric (including its drift terms). -/
theorem normalizedSecondLaplacian_eq_mul_fluxDiv (g1 g2 : MatrixField) (L lam : ℝ)
    (u : R3 → ℝ) (x : R3) :
    normalizedSecondLaplacian g1 g2 L lam u x =
      normalizedSecondLaplacianScalarJoint g1 g2 L (lam,x) *
        (vol (dilatedMetric g2 lam) x)⁻¹ *
          coordinateFluxDivergence (metricDivergenceFlux (dilatedMetric g2 lam) u) x := by
  unfold normalizedSecondLaplacian
  congr 1
  unfold AngularPolynomial.densityWeightedDivergence coordinateFluxDivergence
  refine Finset.sum_congr rfl fun i _ => ?_
  have hb : (EuclideanSpace.basisFun (Fin 3) ℝ) i = coordinateVector i := by
    simp [coordinateVector]
  have hfun : (fun y => vol (dilatedMetric g2 lam) y *
      inner ℝ (MetricOperator.matrixOperatorMap ((dilatedMetric g2 lam y)⁻¹)
        (gradient u y)) ((EuclideanSpace.basisFun (Fin 3) ℝ) i)) =
      fun y => metricDivergenceFlux (dilatedMetric g2 lam) u y i := by
    funext y
    simp only [metricDivergenceFlux]
    show _ = (MetricOperator.matrixOperatorMap
      (vol (dilatedMetric g2 lam) y • (dilatedMetric g2 lam y)⁻¹) (gradient u y)) i
    rw [map_smul]
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right]
  rw [hfun, hb]
  rfl

/-- Transport of the ORIGINAL off-pole row equation through the actual branch,
the carrier identity and the spatial dilation, with the factor `lam`. -/
theorem dilatedRow_fluxDiv_zero (S : KnownSideSourceData) (gO : MatrixField)
    (hgO : IsAdmissibleMetric gO)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSeparatelySmoothInverseSourceKernel gO hgO K G)
    (Xi : R3 → R3) (hXi : ContDiffOn ℝ ∞ Xi S.coordinateRoom)
    (hinj : Set.InjOn Xi S.coordinateRoom)
    (hjac : ∀ x ∈ S.coordinateRoom, IsUnit (coordinateJacobianMatrix Xi x).det)
    (hroom : ∀ x ∈ S.coordinateRoom, Xi x ∈ (radiusTwoOpens : Set R3))
    (gc : MatrixField) (hgc : IsAdmissibleMetric gc)
    (hcar : EqOn gc (pullbackMetric gO Xi) S.coordinateRoom)
    (lam : ℝ) (hlam : 0 < lam) (a x : R3) (ha : a ∈ S.coordinateRoom)
    (hx : lam • x ∈ S.coordinateRoom) (hne : lam • x ≠ a) :
    coordinateFluxDivergence (metricDivergenceFlux (fun z => gc (lam • z))
      (fun z => lam * G ⟨Xi a, hroom a ha⟩ (Xi (lam • z)))) x = 0 := by
  set p : (radiusTwoOpens : Set R3) := ⟨Xi a, hroom a ha⟩ with hp
  have hrow := radiusTwoSourceKernel_row_contDiffOn_and_nativeMetricDifferential_eq_zero
    S.hreg S.hcalc gO hgO K G hData.1 p
  have hTopen : IsOpen ((radiusTwoOpens : Set R3) \ {(p : R3)}) :=
    radiusTwoOpens.isOpen.sdiff isClosed_singleton
  have hUopen : IsOpen (S.coordinateRoom \ {a}) :=
    S.coordinateRoom_open.sdiff isClosed_singleton
  have hmaps : MapsTo Xi (S.coordinateRoom \ {a})
      ((radiusTwoOpens : Set R3) \ {(p : R3)}) := fun y hy =>
    ⟨hroom y hy.1, fun h =>
      hy.2 (mem_singleton_iff.mpr (hinj hy.1 ha (mem_singleton_iff.mp h)))⟩
  have hw : ContDiffOn ℝ ∞ (fun z => G p (Xi z)) (S.coordinateRoom \ {a}) :=
    hrow.1.comp (hXi.mono diff_subset) hmaps
  have hxU : lam • x ∈ S.coordinateRoom \ {a} := ⟨hx, hne⟩
  rw [fluxDiv_const_mul (fun z => gc (lam • z)) (fun z => G p (Xi (lam • z))) x lam
    hlam.ne']
  rw [coordinateFluxDivergence_metricDivergenceFlux_dilation_of_contDiffOn gc hgc lam
    (S.coordinateRoom \ {a}) hUopen (fun z => G p (Xi z)) hw x hxU]
  have hmet : gc =ᶠ[𝓝 (lam • x)] pullbackMetric gO Xi := by
    filter_upwards [S.coordinateRoom_open.mem_nhds hx] with y hy using hcar hy
  rw [fluxDiv_congr_metric gc (pullbackMetric gO Xi) _ _ hmet]
  have hpull := coordinateFluxDivergence_pullbackMetric_of_contDiffOn gO hgO.smooth
    hgO.posDef Xi (G p) S.coordinateRoom ((radiusTwoOpens : Set R3) \ {(p : R3)})
    S.coordinateRoom_open hTopen hXi hrow.1 (lam • x) hx (hmaps hxU) (hjac _ hx)
  have hzero : coordinateFluxDivergence (metricDivergenceFlux gO (G p))
      (Xi (lam • x)) = 0 := by
    have h0 := hrow.2 _ (hmaps hxU)
    rw [nativeMetricDifferential_eq_neg_coordinateFluxDivergence] at h0
    exact neg_eq_zero.mp h0
  have hcomp : (fun z => G p (Xi z)) = G p ∘ Xi := rfl
  rw [hcomp, hpull, hzero]
  simp

/-- Actual lower-cross construction, with transport and the two literal PDEs. -/
theorem initial_cross_product : InitialCrossProductGoal := by
  intro S L lam hlam
  have hsc : Continuous fun z : R3 => lam • z := continuous_const_smul lam
  refine ⟨initialCross_isOpen S lam, ⟨initialKernel_contDiffOn S lam hlam, ?_, ?_⟩, ?_, ?_⟩
  · -- first literal equation, in the x variable
    rintro v ⟨⟨hr1, hr2, hne⟩, hW⟩
    have hne' : lam • v.1 ≠ lam • v.2 := fun h => hne (smul_right_injective R3 hlam.ne' h)
    by_cases h2 : lam • v.2 ∈ S.W
    · have hfun : (fun x => initialKernel S lam (x, v.2)) =
          fun z => lam * S.G1 ⟨S.Xi1 (lam • v.2), S.Xi1_room _ hr2⟩ (S.Xi1 (lam • z)) := by
        funext x
        simp only [initialKernel, if_pos h2, dilatedKernel1, coordinateKernel1, dif_pos hr2]
      rw [hfun]
      exact dilatedRow_fluxDiv_zero S S.original1 S.original1_admissible S.K1 S.G1
        S.kernel1 S.Xi1 S.Xi1_smooth S.Xi1_injective S.Xi1_jacobian S.Xi1_room S.g1
        S.g1_admissible S.carrier1 lam hlam (lam • v.2) v.1 hr2 hr1 hne'
    · have h1 : lam • v.1 ∈ S.W := hW.resolve_right h2
      have hfun : (fun x => initialKernel S lam (x, v.2)) =
          fun z => lam * S.G2 ⟨S.Xi2 (lam • v.2), S.Xi2_room _ hr2⟩ (S.Xi2 (lam • z)) := by
        funext x
        simp only [initialKernel, if_neg h2, dilatedKernel2, coordinateKernel2, dif_pos hr2]
      rw [hfun]
      have hmet : (fun x : R3 => S.g1 (lam • x)) =ᶠ[𝓝 v.1] fun x => S.g2 (lam • x) := by
        filter_upwards [(S.W_open.preimage hsc).mem_nhds h1] with y hy
        exact S.metrics_match hy
      rw [fluxDiv_congr_metric _ _ _ _ hmet]
      exact dilatedRow_fluxDiv_zero S S.original2 S.original2_admissible S.K2 S.G2
        S.kernel2 S.Xi2 S.Xi2_smooth S.Xi2_injective S.Xi2_jacobian S.Xi2_room S.g2
        S.g2_admissible S.carrier2 lam hlam (lam • v.2) v.1 hr2 hr1 hne'
  · -- second literal equation, the native normalized second operator
    rintro v ⟨⟨hr1, hr2, hne⟩, hW⟩
    have hne' : lam • v.2 ≠ lam • v.1 := fun h =>
      hne (smul_right_injective R3 hlam.ne' h).symm
    rw [normalizedSecondLaplacian_eq_mul_fluxDiv]
    suffices hz : coordinateFluxDivergence (metricDivergenceFlux (dilatedMetric S.g2 lam)
        (fun y => initialKernel S lam (v.1, y))) v.2 = 0 by
      rw [hz, mul_zero]
    have hNear : ∀ᶠ y in 𝓝 v.2, lam • y ∈ S.coordinateRoom ∧ y ≠ v.1 := by
      have hA := (S.coordinateRoom_open.preimage hsc).mem_nhds hr2
      have hB := isOpen_ne.mem_nhds (Ne.symm hne)
      filter_upwards [hA, hB] with y hy1 hy2 using ⟨hy1, hy2⟩
    by_cases h1 : lam • v.1 ∈ S.W
    · have hev : (fun y => initialKernel S lam (v.1, y)) =ᶠ[𝓝 v.2]
          fun z => lam * S.G2 ⟨S.Xi2 (lam • v.1), S.Xi2_room _ hr1⟩ (S.Xi2 (lam • z)) := by
        filter_upwards [hNear] with y hy
        rw [initialKernel_eq_dilatedKernel2 S lam hlam (v.1, y) ⟨hr1, hy.1, hy.2.symm⟩ h1]
        simp only [dilatedKernel2, coordinateKernel2, dif_pos hy.1]
        rw [S.kernel2.1.2 ⟨S.Xi2 (lam • y), S.Xi2_room _ hy.1⟩
          ⟨S.Xi2 (lam • v.1), S.Xi2_room _ hr1⟩]
      rw [coordinateFluxDivergence_metricDivergenceFlux_congr_of_eventuallyEq _ _ _ _ hev]
      exact dilatedRow_fluxDiv_zero S S.original2 S.original2_admissible S.K2 S.G2
        S.kernel2 S.Xi2 S.Xi2_smooth S.Xi2_injective S.Xi2_jacobian S.Xi2_room S.g2
        S.g2_admissible S.carrier2 lam hlam (lam • v.1) v.2 hr1 hr2 hne'
    · have h2 : lam • v.2 ∈ S.W := hW.resolve_left h1
      have hWnear := (S.W_open.preimage hsc).mem_nhds h2
      have hev : (fun y => initialKernel S lam (v.1, y)) =ᶠ[𝓝 v.2]
          fun z => lam * S.G1 ⟨S.Xi1 (lam • v.1), S.Xi1_room _ hr1⟩ (S.Xi1 (lam • z)) := by
        filter_upwards [hNear, hWnear] with y hy hyW
        rw [initialKernel_eq_dilatedKernel1 S lam (v.1, y) hyW]
        simp only [dilatedKernel1, coordinateKernel1, dif_pos hy.1]
        rw [S.kernel1.1.2 ⟨S.Xi1 (lam • y), S.Xi1_room _ hy.1⟩
          ⟨S.Xi1 (lam • v.1), S.Xi1_room _ hr1⟩]
      rw [coordinateFluxDivergence_metricDivergenceFlux_congr_of_eventuallyEq _ _ _ _ hev]
      have hmet : dilatedMetric S.g2 lam =ᶠ[𝓝 v.2] fun x => S.g1 (lam • x) := by
        filter_upwards [hWnear] with y hy
        exact (S.metrics_match hy).symm
      rw [fluxDiv_congr_metric _ _ _ _ hmet]
      exact dilatedRow_fluxDiv_zero S S.original1 S.original1_admissible S.K1 S.G1
        S.kernel1 S.Xi1 S.Xi1_smooth S.Xi1_injective S.Xi1_jacobian S.Xi1_room S.g1
        S.g1_admissible S.carrier1 lam hlam (lam • v.1) v.2 hr1 hr2 hne'
  · intro v _ h2
    exact initialKernel_eq_dilatedKernel1 S lam v h2
  · intro v hv h1
    exact initialKernel_eq_dilatedKernel2 S lam hlam v hv.1 h1

/-! ## Endpoint components: parameter selection and room (no kernel is produced) -/

/-- The whole current-radius family stays below any positive ceiling once `Rstar`
is small; `R0` depends only on `L,p` and the ceiling. -/
theorem exists_referenceRadius_lt (L : ℝ) (p : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ Rstar : ℝ, 0 < Rstar → Rstar ≤ R0 →
      ∀ d : ℝ, 0 < d → d ≤ 1 → ∀ y ∈ cylinder, referenceRadius d Rstar p L y < c := by
  obtain ⟨T, hT⟩ := isCompact_cylinder.exists_bound_of_continuousOn
    (contDiff_referenceDepth L).continuous.continuousOn
  set A : ℝ := Real.log (1 + Real.exp T)
  have hA : 0 < A := Real.log_pos (by linarith [Real.exp_pos T])
  have hAp : 0 < A ^ p + 1 := by positivity
  refine ⟨c / (A ^ p + 1), div_pos hc hAp, fun Rstar hR hRle d hd hd1 y hy => ?_⟩
  have hdep : referenceDepth L y ≤ T :=
    (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hT y hy)
  have hs := RadiusProfile.softplus_le_log_exp_upper d (referenceDepth L y) T hd hd1 hdep
  have hs0 := (RadiusProfile.softplus_pos d (referenceDepth L y) hd).le
  have hpow : (RadiusProfile.softplus d (referenceDepth L y)) ^ p ≤ A ^ p :=
    pow_le_pow_left₀ hs0 hs p
  unfold referenceRadius
  calc Rstar * (RadiusProfile.softplus d (referenceDepth L y)) ^ p ≤ c / (A ^ p + 1) * A ^ p :=
        mul_le_mul hRle hpow (pow_nonneg hs0 p) (div_pos hc hAp).le
    _ < c := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hAp]
        nlinarith

/-- A dilation ceiling putting a fixed ball into the coordinate room. -/
theorem exists_dilation_room (S : KnownSideSourceData) (bound : ℝ) :
    ∃ lam1 : ℝ, 0 < lam1 ∧ ∀ lam : ℝ, 0 ≤ lam → lam ≤ lam1 → ∀ x : R3, ‖x‖ ≤ max bound 2 →
      lam • x ∈ S.coordinateRoom := by
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.1 S.coordinateRoom_open 0 S.origin_mem
  set m := max bound 2
  have hm : 0 < m + 1 := by have := le_max_right bound 2; linarith
  refine ⟨a / (m + 1), div_pos ha hm, fun lam hl0 hl x hx => hball ?_⟩
  rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl0]
  calc lam * ‖x‖ ≤ a / (m + 1) * m := mul_le_mul hl hx (norm_nonneg _) (div_pos ha hm).le
    _ < a := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hm]
        nlinarith

theorem fixedSeparation_subset_dilatedOffDiagonal (S : KnownSideSourceData)
    (bound separation lam : ℝ) (hsep : 0 < separation)
    (hroom : ∀ x : R3, ‖x‖ ≤ bound → lam • x ∈ S.coordinateRoom) :
    fixedSeparationSet bound separation ⊆ dilatedOffDiagonal S lam := by
  rintro v ⟨h1, h2, h3⟩
  refine ⟨hroom _ h1, hroom _ h2, fun h => ?_⟩
  rw [h, sub_self, norm_zero] at h3
  linarith

/-- Every moving-sphere point is off the diagonal: same-flow injectivity and the
zero-velocity endpoint `E(q,y,r,0)=y`. -/
theorem movingSphere_mem_dilatedOffDiagonal (S : KnownSideSourceData) (L : ℝ)
    (cover : NativeNormalCover S L) (i : Fin cover.count) (lam : ℝ)
    (hlam : lam ∈ Icc (0 : ℝ) cover.dilationCeiling) (y : R3)
    (hy : y ∈ (cover.packet i).centers) (hyroom : lam • y ∈ S.coordinateRoom)
    (r : ℝ) (hr : 0 < r) (hrc : r < cover.radiusCeiling)
    (z : R3) (hz : z ∈ sphere (0 : R3) 1) :
    (packetEndpoint S L (cover.packet i) lam y r z, y) ∈ dilatedOffDiagonal S lam := by
  have hz2 : z ∈ closedBall (0 : R3) 2 := by
    rw [mem_sphere, dist_zero_right] at hz
    rw [mem_closedBall, dist_zero_right]
    linarith
  refine ⟨cover.coordinate_room i lam hlam y hy r hr hrc z hz2, hyroom, ?_⟩
  intro heq
  have hq : lam ∈ Icc (0 : ℝ) 1 := ⟨hlam.1, hlam.2.trans cover.dilation_le_one⟩
  obtain ⟨hE, -⟩ := packet_room S L (cover.packet i)
  obtain ⟨-, -, -, -, -, -, -, -, hvalue, -⟩ := hE
  have h0 : packetEndpoint S L (cover.packet i) lam y r 0 = y := by
    show ((cover.packet i).Phi lam
      (y, r • conformalReferenceGramFrameOperatorJoint S.g1 L (lam, y) 0) 1).1 = y
    rw [map_zero, smul_zero]
    exact hvalue lam hq y ((cover.packet i).centers_room y hy).2
  have hinj := cover.normal_injective i lam hlam y hy r hr hrc hz2
    (mem_closedBall_self (by norm_num)) (heq.trans h0.symm)
  rw [hinj, mem_sphere, dist_self] at hz
  norm_num at hz

/-- COMPONENT, not the endpoint: the endpoint's full quantifier skeleton, the
cover returned before the shrinking parameters, its first conjunct, and the
room of BOTH required domain pieces inside the dilated off-diagonal. The
mixed kernel itself is NOT produced here. -/
theorem actual_mixed_kernel_parameter_room :
    ∀ (S : KnownSideSourceData) (bound separation : ℝ), 0 < bound → 0 < separation →
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∃ cover : NativeNormalCover S L,
    ∃ p0 : ℕ, 2 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p →
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 ∧
    ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ Rstar : ℝ, 0 < Rstar → Rstar ≤ R0 →
    ∃ lam0 : ℝ, 0 < lam0 ∧ lam0 ≤ cover.dilationCeiling ∧
    ∀ lam : ℝ, 0 < lam → lam ≤ lam0 →
    ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
    (∀ delta' ∈ Icc delta (1 : ℝ), ∀ y ∈ cylinder,
      referenceRadius delta' Rstar p L y < cover.radiusCeiling) ∧
    fixedSeparationSet bound separation ⊆ dilatedOffDiagonal S lam ∧
    ∀ i, ∀ y ∈ cylinder ∩ (cover.packet i).centers, ∀ z ∈ sphere (0 : R3) 1,
      (packetEndpoint S L (cover.packet i) lam y (referenceRadius delta Rstar p L y) z, y) ∈
        dilatedOffDiagonal S lam := by
  intro S bound separation _ hsep
  refine ⟨1, one_pos, fun L hL => ?_⟩
  obtain ⟨cover⟩ := normal_packet_cover_exists S L (by linarith)
  refine ⟨cover, 2, le_rfl, fun p _ => ⟨1, one_pos, le_rfl, fun eps _ _ => ?_⟩⟩
  obtain ⟨R0, hR0, hrad⟩ :=
    exists_referenceRadius_lt L p cover.radiusCeiling cover.radius_positive
  refine ⟨R0, hR0, fun Rstar hR hRle => ?_⟩
  obtain ⟨lam1, hlam1, hroom⟩ := exists_dilation_room S bound
  refine ⟨min lam1 cover.dilationCeiling, lt_min hlam1 cover.dilation_positive,
    min_le_right _ _, fun lam hl hlle delta hd hd1 => ⟨?_, ?_, ?_⟩⟩
  · intro d hdI y hy
    exact hrad Rstar hR hRle d (hd.trans_le hdI.1) hdI.2 y hy
  · exact fixedSeparation_subset_dilatedOffDiagonal S bound separation lam hsep
      (fun x hx => hroom lam hl.le (hlle.trans (min_le_left _ _)) x
        (hx.trans (le_max_left _ _)))
  · rintro i y ⟨hyc, hyi⟩ z hz
    exact movingSphere_mem_dilatedOffDiagonal S L cover i lam
      ⟨hl.le, hlle.trans (min_le_right _ _)⟩ y hyi
      (hroom lam hl.le (hlle.trans (min_le_left _ _)) y
        ((norm_le_two_of_mem_cylinder hyc).trans (le_max_right _ _)))
      _ (referenceRadius_pos delta Rstar p L y hd hR)
      (hrad Rstar hR hRle delta hd hd1 y hyc) z hz

/-! ### C3-D1: jet-evaluation CLMs on the closed native harmonic L² space

One fixed scalar coefficient `A` on an open room `D`. Every result below is derived from the
closure444/416 theorems; no approximation, compactness or spectral premise is used. -/
end OAI.AnisotropicCalderon.MixedKernelConstructionTask.Geometry
