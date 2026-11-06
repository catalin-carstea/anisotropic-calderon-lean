import Calderon.ActualUniformFiniteFormalAdjointPhysicalL2
import Calderon.ActualFiniteCoreSobolevRepresentation
import Calderon.ActualFullAdjointFirstActionRegularity
import Calderon.ActualFiniteHighFullAdjointFirstSectionSupport
import Calderon.SphereSobolevPairing

/-! The original finite INPUT cutoff and literal uncompressed Half section.
Full author expansion: full-physical-graph-and-genuine-adjoint-beforecode-v001.
No finite output, inverse negative inclusion, norm change or Products premise. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.MainPhysicalGraphBridge
open EnergyBridge ConnectionError SphereHarmonic ActualFiniteHarmonicCore
  SpectralWeightedGraph SmoothMetricFrame MovingFrameConnection

def physicalL2Inclusion (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) :
    SphereL2 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp
    (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap

theorem dualPairing_negative_half_physicalL2Inclusion
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (V : SphereL2) (U : SphereSobolev (3/2 : ℝ)) :
  sphereSobolevDualPairing (-(1/2 : ℝ)) (physicalL2Inclusion hO hD V)
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) U) =
  ⟪V, (sphereSobolevZeroEquiv hO hD).symm
    (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) U)⟫_ℝ := by
  let Z := sphereSobolevZeroEquiv hO hD
  have hZero : sphereSobolevDualPairing (-(1/2 : ℝ))
      (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) (Z V))
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) U) =
      ⟪Z V, sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) U⟫_ℝ := by
    rw [sphereSobolevDualPairing_eq_tsum, inner_sphereSobolev 0]
    apply tsum_congr
    intro k
    have hU : sphereSobolevCoefficientL (-(-(1/2 : ℝ))) k
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) U) =
        sphereSobolevCoefficientL (3/2 : ℝ) k U := by
      have hIndex := congrArg
        (fun t : ℝ => sphereSobolevCoefficientL t k
          (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) U))
        (neg_neg (1/2 : ℝ))
      exact hIndex.trans
        (sphereSobolevCoefficientL_inclusion (3/2 : ℝ) (1/2 : ℝ) (by norm_num) U k)
    simp only [hU, sphereSobolevCoefficientL_inclusion,
      besselWeight_zero_order, one_pow, one_mul]
  change sphereSobolevDualPairing (-(1/2 : ℝ))
    (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) (Z V))
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) U) = _
  refine hZero.trans ?_
  have h := Z.inner_map_map V
    (Z.symm (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) U))
  rw [Z.apply_symm_apply] at h
  exact h

theorem dualPairing_half_physicalL2Inclusion
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (U : SphereSobolev (3/2 : ℝ)) (V : SphereL2) :
  sphereSobolevDualPairing (1/2 : ℝ)
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) U)
    (physicalL2Inclusion hO hD V) =
  ⟪(sphereSobolevZeroEquiv hO hD).symm
    (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) U), V⟫_ℝ := by
  let Z := sphereSobolevZeroEquiv hO hD
  have hZero : sphereSobolevDualPairing (1/2 : ℝ)
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) U)
      (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) (Z V)) =
      ⟪sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) U, Z V⟫_ℝ := by
    rw [sphereSobolevDualPairing_eq_tsum, inner_sphereSobolev 0]
    apply tsum_congr
    intro k
    simp only [sphereSobolevCoefficientL_inclusion,
      besselWeight_zero_order, one_pow, one_mul]
  change sphereSobolevDualPairing (1/2 : ℝ)
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) U)
    (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) (Z V)) = _
  refine hZero.trans ?_
  have h := Z.inner_map_map
    (Z.symm (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) U)) V
  rw [Z.apply_symm_apply] at h
  exact h

private lemma tsupport_subset_of_zero_off {E : Type*} [Zero E]
    (f : R3 → E) (K : Set R3) (hK : IsClosed K)
    (hZero : ∀ x ∉ K, f x = 0) : tsupport f ⊆ K := by
  change closure (Function.support f) ⊆ K
  apply closure_minimal ?_ hK
  intro x hx
  by_contra hNot
  change f x ≠ 0 at hx
  exact hx (hZero x hNot)

private theorem mapped_section_properties
    {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    (T : E →L[ℝ] F) (K : F →L[ℝ] G) (J : E →L[ℝ] G)
    (hMap : ∀ v : E, K (T v) = J v)
    (W : R3 → E) (V : R3 → G) (S : Set R3)
    (hWSmooth : ContDiff ℝ ∞ W) (hWCompact : HasCompactSupport W)
    (hWSupport : tsupport W ⊆ S) (hGraph : ∀ x : R3, J (W x) = V x) :
  ContDiff ℝ ∞ (fun x : R3 => T (W x)) ∧
  HasCompactSupport (fun x : R3 => T (W x)) ∧
  MemLp (fun x : R3 => T (W x)) (2 : ℝ≥0∞) (volume : Measure R3) ∧
  tsupport (fun x : R3 => T (W x)) ⊆ S ∧
  ∀ x : R3, K (T (W x)) = V x := by
  have hSmooth : ContDiff ℝ ∞ (fun x : R3 => T (W x)) := T.contDiff.comp hWSmooth
  have hSupport : tsupport (fun x : R3 => T (W x)) ⊆ tsupport W :=
    tsupport_comp_subset (map_zero T) W
  have hCompact : HasCompactSupport (fun x : R3 => T (W x)) :=
    hWCompact.of_isClosed_subset (isClosed_tsupport _) hSupport
  have hMem : MemLp (fun x : R3 => T (W x)) (2 : ℝ≥0∞) (volume : Measure R3) :=
    hSmooth.continuous.memLp_of_hasCompactSupport hCompact
  exact ⟨hSmooth, hCompact, hMem, hSupport.trans hWSupport,
    fun x => (hMap (W x)).trans (hGraph x)⟩

private lemma physicalL2Inclusion_half_postmap
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (v : SphereSobolev (1/2 : ℝ)) :
  physicalL2Inclusion hO hD ((sphereSobolevZeroEquiv hO hD).symm
    (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) v)) =
  sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) v := by
  have hCancel := congrArg (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num))
    ((sphereSobolevZeroEquiv hO hD).apply_symm_apply
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) v))
  have hTrans := congrArg
    (fun T : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T v)
    (sphereSobolevInclusionL_trans (1/2 : ℝ) 0 (-(1/2 : ℝ)) (by norm_num) (by norm_num))
  exact hCancel.trans hTrans

private theorem canonical_half_section_properties
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (W : R3 → SphereSobolev (1/2 : ℝ))
    (V : R3 → SphereSobolev (-(1/2 : ℝ))) (S : Set R3)
    (hWSmooth : ContDiff ℝ ∞ W) (hWCompact : HasCompactSupport W)
    (hWSupport : tsupport W ⊆ S)
    (hGraph : ∀ x : R3,
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (W x) = V x) :
  let Y : R3 → SphereL2 := fun x => (sphereSobolevZeroEquiv hO hD).symm
    (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (W x))
  ContDiff ℝ ∞ Y ∧ HasCompactSupport Y ∧ MemLp Y 2 (volume : Measure R3) ∧
  tsupport Y ⊆ S ∧ ∀ x : R3, physicalL2Inclusion hO hD (Y x) = V x := by
  have hMidSmooth : ContDiff ℝ ∞ (fun x : R3 =>
      sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (W x)) :=
    (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)).contDiff.comp hWSmooth
  have hYSmooth : ContDiff ℝ ∞ (fun x : R3 => (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (W x))) :=
    (sphereSobolevZeroEquiv hO hD).symm.contDiff.comp hMidSmooth
  have hMidSupport : tsupport (fun x : R3 =>
      sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (W x)) ⊆ tsupport W :=
    tsupport_comp_subset (map_zero (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num))) W
  have hYSupportMid : tsupport (fun x : R3 => (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (W x))) ⊆
      tsupport (fun x : R3 => sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (W x)) :=
    tsupport_comp_subset (map_zero ((sphereSobolevZeroEquiv hO hD).symm))
      (fun x : R3 => sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (W x))
  have hYSupport : tsupport (fun x : R3 => (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (W x))) ⊆ tsupport W :=
    hYSupportMid.trans hMidSupport
  have hYCompact : HasCompactSupport (fun x : R3 => (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (W x))) :=
    hWCompact.of_isClosed_subset (isClosed_tsupport _) hYSupport
  have hYMem : MemLp (fun x : R3 => (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (W x))) 2 (volume : Measure R3) :=
    hYSmooth.continuous.memLp_of_hasCompactSupport hYCompact
  refine ⟨hYSmooth, hYCompact, hYMem, hYSupport.trans hWSupport, ?_⟩
  intro x
  exact (physicalL2Inclusion_half_postmap hO hD (W x)).trans (hGraph x)

section OriginalData
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

private lemma tsupport_finiteHalfFormalAdjointPhysicalSection_subset
    (g2 : MatrixField) (n : ℕ) (q : ℝ) (R : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) :
  tsupport (fun x => referenceFiniteHalfFormalAdjointPhysicalSection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 n q R u x) ⊆ tsupport u := by
  have hScalar (c : R3 → ℝ) : tsupport (fun x => c x • u x) ⊆ tsupport u := by
    apply tsupport_subset_of_zero_off _ _ (isClosed_tsupport u)
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]
  have hPartial (c : R3 → ℝ) :
      tsupport (fun x => sphereSobolevPartialSumL (3/2 : ℝ) n (c x • u x)) ⊆ tsupport u := by
    apply tsupport_subset_of_zero_off _ _ (isClosed_tsupport u)
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, smul_zero, map_zero]
  apply tsupport_subset_of_zero_off _ _ (isClosed_tsupport u)
  intro x hx
  have hXi (c : R3 → ℝ) (i j : Fin 3) :
      referenceHighFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun z => referenceFiniteHighFullAdjointFirstSection
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R
          (fun y => c y • u y) z i) x j = 0 := by
    have hEta := tsupport_referenceFiniteHighFullAdjointFirstSection_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R
      (fun y => c y • u y) i
    have hY := tsupport_referenceHighFullAdjointFirstAction_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
      (fun z => referenceFiniteHighFullAdjointFirstSection
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R
        (fun y => c y • u y) z i) j
    have hxY : x ∉ tsupport (fun z : R3 => referenceHighFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun z => referenceFiniteHighFullAdjointFirstSection
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R
          (fun y => c y • u y) z i) z j) :=
      fun h => hx ((hY.trans (hEta.trans (hScalar c))) h)
    exact image_eq_zero_of_notMem_tsupport
      (f := fun z : R3 => referenceHighFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun z => referenceFiniteHighFullAdjointFirstSection
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R
          (fun y => c y • u y) z i) z j) (x := x) hxY
  have hY (c : R3 → ℝ) (i : Fin 3) :
      referenceHighFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun z => sphereSobolevPartialSumL (3/2 : ℝ) n (c z • u z)) x i = 0 := by
    have hs := tsupport_referenceHighFullAdjointFirstAction_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
      (fun z => sphereSobolevPartialSumL (3/2 : ℝ) n (c z • u z)) i
    have hxY : x ∉ tsupport (fun z : R3 => referenceHighFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun z => sphereSobolevPartialSumL (3/2 : ℝ) n (c z • u z)) z i) :=
      fun h => hx ((hs.trans (hPartial c)) h)
    exact image_eq_zero_of_notMem_tsupport
      (f := fun z : R3 => referenceHighFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R
        (fun z => sphereSobolevPartialSumL (3/2 : ℝ) n (c z • u z)) z i) (x := x) hxY
  simp only [referenceFiniteHalfFormalAdjointPhysicalSection, hXi, hY,
    Finset.sum_const_zero, sub_zero, add_zero]

private theorem exists_common_radius_half_formal_adjoint_section_properties
    (hreg : FixedDirichletRegularity) :
  ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ ρ ∧
  ∀ (g2 : MatrixField), IsAdmissibleMetric g2 →
  ∀ (n : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
  ∀ R : R3 → ℝ, ContDiff ℝ ∞ R →
  ∀ u : R3 → SphereSobolev (3/2 : ℝ), ContDiff ℝ ∞ u → HasCompactSupport u →
  (∀ x ∈ tsupport u, ‖x-y0‖ < ρ ∧ |R x| < d0 ∧ R x ≠ 0) →
  let W : R3 → SphereSobolev (1/2 : ℝ) := fun x => referenceFiniteHalfFormalAdjointPhysicalSection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 n q R u x
  ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧ tsupport W ⊆ tsupport u ∧
  ∀ x : R3, sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (W x) =
    referenceFormalAdjointPhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
      (fun z => sphereSobolevPartialSumL (3/2 : ℝ) n (u z)) x := by
  obtain ⟨dG, hdG, hdGρ, hGraph⟩ :=
    exists_reference_commonRadius_finiteFormalAdjointPhysicalSection_graph_uniform_metric
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  obtain ⟨dS, hdS, hdSρ, hGlobal⟩ :=
    exists_reference_commonRadius_finiteFormalAdjointPhysicalSection_global_uniform_metric
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  refine ⟨min dG dS, lt_min hdG hdS, (min_le_left _ _).trans hdGρ, ?_⟩
  intro g2 hg2 n q hq R hR u hu hCompact hRoom
  have hRoomG : ∀ x ∈ tsupport u, ‖x-y0‖ < ρ ∧ |R x| < dG ∧ R x ≠ 0 := by
    intro x hx
    have h := hRoom x hx
    exact ⟨h.1, h.2.1.trans_le (min_le_left _ _), h.2.2⟩
  have hRoomS : ∀ x ∈ tsupport u, ‖x-y0‖ < ρ ∧ |R x| < dS ∧ R x ≠ 0 := by
    intro x hx
    have h := hRoom x hx
    exact ⟨h.1, h.2.1.trans_le (min_le_right _ _), h.2.2⟩
  have hRegularity := hGlobal g2 hg2 n q hq R hR u hu hCompact hRoomS
  have hSupport := tsupport_finiteHalfFormalAdjointPhysicalSection_subset
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 n q R u
  exact ⟨hRegularity.1, hRegularity.2, hSupport,
    hGraph g2 hg2 n q hq R hR u hu hCompact hRoomG⟩

set_option diagnostics true in
theorem exists_common_radius_finite_input_formal_adjoint_output
    (hreg : FixedDirichletRegularity) :
  ∃ dAdj : ℝ, 0 < dAdj ∧ dAdj ≤ ρ ∧
  ∀ (g2 : MatrixField), IsAdmissibleMetric g2 →
  ∀ q ∈ Icc (0 : ℝ) 1, ∀ R : R3 → ℝ, ContDiff ℝ ∞ R →
  ∀ G : smoothCompactFiniteSphereCore hO hD,
  (∀ x ∈ tsupport G.val, ‖x-y0‖ < ρ ∧ |R x| < dAdj ∧ R x ≠ 0) →
  ∃ n : ℕ,
    (fun x => sphereSobolevPartialSumL (3/2 : ℝ) n
      (finiteCoreSobolevLift hO hD (3/2 : ℝ) G x)) =
      finiteCoreSobolevLift hO hD (3/2 : ℝ) G ∧
    let Y : R3 → SphereL2 := fun x => (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (referenceFiniteHalfFormalAdjointPhysicalSection
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 n q R
          (finiteCoreSobolevLift hO hD (3/2 : ℝ) G) x))
    ContDiff ℝ ∞ Y ∧ HasCompactSupport Y ∧ MemLp Y 2 (volume : Measure R3) ∧
    tsupport Y ⊆ tsupport G.val ∧
    ∀ x : R3, physicalL2Inclusion hO hD (Y x) =
      referenceFormalAdjointPhysicalDensityOperator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) G) x := by
  obtain ⟨d0, hd0, hd0ρ, hSection⟩ :=
    exists_common_radius_half_formal_adjoint_section_properties
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  refine ⟨d0, hd0, hd0ρ, ?_⟩
  intro g2 hg2 q hq R hR G hRoom
  let u : R3 → SphereSobolev (3/2 : ℝ) := finiteCoreSobolevLift hO hD (3/2 : ℝ) G
  have hRepresentation :=
    finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) G
  rcases hRepresentation with ⟨hu, huCompact, huSupport, huZero, n, hn⟩
  have hRoomU : ∀ x ∈ tsupport u, ‖x-y0‖ < ρ ∧ |R x| < d0 ∧ R x ≠ 0 := by
    intro x hx
    exact hRoom x (huSupport hx)
  have hProperties := hSection g2 hg2 n q hq R hR u hu huCompact hRoomU
  rcases hProperties with ⟨hWSmooth, hWCompact, hWSupport, hWGraph⟩
  let W : R3 → SphereSobolev (1/2 : ℝ) := fun x => referenceFiniteHalfFormalAdjointPhysicalSection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 n q R u x
  let J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let V : R3 → SphereSobolev (-(1/2 : ℝ)) := fun x =>
    referenceFormalAdjointPhysicalDensityOperator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R u x
  have hGraph : ∀ x : R3, J (W x) = V x := by
    intro x
    exact (hWGraph x).trans (congrArg
      (fun f : R3 → SphereSobolev (3/2 : ℝ) =>
        referenceFormalAdjointPhysicalDensityOperator
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 q R f x) hn)
  have hMapped := canonical_half_section_properties hO hD W V (tsupport G.val)
    hWSmooth hWCompact (hWSupport.trans huSupport) hGraph
  dsimp only [W, u, V, J] at hMapped
  refine ⟨n, hn, ?_, ?_, ?_, ?_, ?_⟩
  · exact hMapped.1
  · exact hMapped.2.1
  · exact hMapped.2.2.1
  · exact hMapped.2.2.2.1
  · intro x
    exact hMapped.2.2.2.2 x
end OriginalData
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.MainPhysicalGraphBridge

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.MainPhysicalGraphBridge.dualPairing_negative_half_physicalL2Inclusion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.MainPhysicalGraphBridge.dualPairing_half_physicalL2Inclusion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.MainPhysicalGraphBridge.exists_common_radius_finite_input_formal_adjoint_output
