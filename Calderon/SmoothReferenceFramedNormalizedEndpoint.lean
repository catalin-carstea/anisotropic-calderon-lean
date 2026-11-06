import Calderon.ActualCompactNormalChart
import Calderon.ParameterHadamardDivision

/-! Source-only same-witness author construction. EXPANSION-v001.md is sealed.
The new integral representative is globally smooth. It is proved equal to the
unchanged piecewise endpoint on the exact closed-q normalization domain.
No ambient germ equality across its closed-q boundary is asserted. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError

private instance instCompleteSmoothFramedEndpointR3 : CompleteSpace R3 :=
  FiniteDimensional.complete ℝ R3

/-- Literal displacement of the same physical endpoint, reassociated by radius. -/
def referenceFramedEndpointDisplacement (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (a : (ℝ × (R3 × R3)) × ℝ) : R3 :=
  referenceFramedPhysicalEndpoint g L Φ (a.1.1,((a.1.2.1,a.2),a.1.2.2)) - a.1.2.1

/-- Canonical smooth derivative-average of the actual displacement; no flow is replaced. -/
def referenceFramedNormalizedEndpointIntegral (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (a : ReferenceEndpointVariables) : R3 :=
  parameterHadamardDivision (referenceFramedEndpointDisplacement g L Φ)
    ((a.1,(a.2.1.1,a.2.2)),a.2.1.2)

/-- The exact exported zero-value and first-jet authority, with arbitrary signed r and z. -/
def referenceFramedNormalizationDomain (B : Set (R3 × R3)) : Set ReferenceEndpointVariables :=
  {a | a.1 ∈ Icc (0 : ℝ) 1 ∧ (a.2.1.1,0) ∈ B}

theorem contDiff_referenceFramedEndpointDisplacement (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (Φ a.1 a.2 1).1)) :
    ContDiff ℝ ∞ (referenceFramedEndpointDisplacement g L Φ) :=
  ((contDiff_referenceFramedPhysicalEndpoint g hg L Φ hΘ).comp
    (contDiff_fst.fst.prodMk
      ((contDiff_fst.snd.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd.snd))).sub
        contDiff_fst.snd.fst

theorem contDiff_referenceFramedNormalizedEndpointIntegral (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (Φ a.1 a.2 1).1)) :
    ContDiff ℝ ∞ (referenceFramedNormalizedEndpointIntegral g L Φ) :=
  (contDiff_parameterHadamardDivision _
    (contDiff_referenceFramedEndpointDisplacement g hg L Φ hΘ)).comp
      ((contDiff_fst.prodMk (contDiff_snd.fst.fst.prodMk contDiff_snd.snd)).prodMk
        contDiff_snd.fst.snd)

/-- Exact division identifies both the nonzero quotient and the original frame value at zero. -/
theorem referenceFramedNormalizedEndpointIntegral_eq (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (Φ a.1 a.2 1).1))
    (q : ℝ) (y z : R3) (r : ℝ) (hzero : (Φ q (y,0) 1).1 = y)
    (hfirst : HasFDerivAt (fun a => (Φ q a 1).1)
      (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (y,0)) :
    referenceFramedNormalizedEndpointIntegral g L Φ (q,((y,r),z)) =
      referenceFramedNormalizedEndpoint g L Φ (q,((y,r),z)) := by
  let H := referenceFramedEndpointDisplacement g L Φ
  let p : ℝ × (R3 × R3) := (q,(y,z))
  let v : R3 := conformalReferenceGramFrameOperatorJoint g L (q,y) z
  have hH : ContDiff ℝ ∞ H := contDiff_referenceFramedEndpointDisplacement g hg L Φ hΘ
  have hH0 : H (p,0) = 0 := by
    simp only [H,p,referenceFramedEndpointDisplacement,referenceFramedPhysicalEndpoint,
      zero_smul,hzero,sub_self]
  by_cases hr : r = 0
  · subst r
    have hi : HasDerivAt (fun s : ℝ => (y,s • v)) (0,v) 0 := by
      convert (hasDerivAt_const (0 : ℝ) y).prodMk
        ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1 <;>
        simp only [id_eq,one_smul]
    have hpos : HasDerivAt (fun s : ℝ => (Φ q (y,s • v) 1).1) v 0 := by
      have hc := hfirst.comp_hasDerivAt_of_eq (0 : ℝ) hi (by simp)
      simpa only [Function.comp_def,ContinuousLinearMap.add_apply,
        ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',zero_add] using hc
    have hd : HasDerivAt (fun s : ℝ => H (p,s)) v 0 := by
      convert hpos.sub (hasDerivAt_const (0 : ℝ) y) using 1 <;>
        first | rfl | simp only [sub_zero]
    change parameterHadamardDivision H (p,0) =
      referenceFramedNormalizedEndpoint g L Φ (q,((y,0),z))
    rw [parameterHadamardDivision_zero_eq_deriv H hH p,hd.deriv,
      referenceFramedNormalizedEndpoint_zero]
  · change parameterHadamardDivision H (p,r) =
      referenceFramedNormalizedEndpoint g L Φ (q,((y,r),z))
    rw [parameterHadamardDivision_eq_inv_smul H hH p r hH0 hr]
    simp only [H,p,referenceFramedEndpointDisplacement,referenceFramedNormalizedEndpoint,
      if_neg hr]

theorem referenceFramedNormalizedEndpoint_eqOn_integral (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
    (hData : ConformalReferenceGeodesicEndpointData g L y0 Φ B) :
    EqOn (referenceFramedNormalizedEndpoint g L Φ)
      (referenceFramedNormalizedEndpointIntegral g L Φ) (referenceFramedNormalizationDomain B) := by
  rcases hData with ⟨_,_,_,_,_,_,_,hΘ,hvalue,hfirst,_⟩
  intro a ha
  exact (referenceFramedNormalizedEndpointIntegral_eq g hg L Φ hΘ
    a.1 a.2.1.1 a.2.2 a.2.1.2
    (hvalue a.1 ha.1 a.2.1.1 ha.2) (hfirst a.1 ha.1 a.2.1.1 ha.2)).symm

/-- Joint smoothness within the exact closed-q domain, furnished by a genuine smooth extension. -/
theorem contDiffOn_referenceFramedNormalizedEndpoint (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3))
    (hData : ConformalReferenceGeodesicEndpointData g L y0 Φ B) :
    ContDiffOn ℝ ∞ (referenceFramedNormalizedEndpoint g L Φ) (referenceFramedNormalizationDomain B) := by
  have heq := referenceFramedNormalizedEndpoint_eqOn_integral g hg L y0 Φ B hData
  rcases hData with ⟨_,_,_,_,_,_,_,hΘ,_,_,_⟩
  exact (contDiff_referenceFramedNormalizedEndpointIntegral g hg L Φ hΘ).contDiffOn.congr heq

theorem referenceFramedMetricRoom_subset_normalizationDomain (g : MatrixField)
    (L : ℝ) (y0 : R3) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (B : Set (R3 × R3)) (ε C : ℝ)
    (hData : ConformalReferenceFramedMetricData g L y0 Φ B ε C) :
    conformalReferenceFramedMetricRoom y0 ε ⊆ referenceFramedNormalizationDomain B := by
  rcases hData with ⟨_,hε,_,_,_,_,hroom,_⟩
  intro a ha
  have hy : ‖a.2.1.1-y0‖ ≤ ε := by
    simpa only [mem_closedBall,dist_eq_norm] using ha.2.1.1
  refine ⟨ha.1,?_⟩
  have hphase := (hroom a.1 ha.1 a.2.1.1 hy 0 (by simpa using hε.le) 0 (by simp)).1
  simpa only [zero_smul] using hphase

/-- Supplied-witness form: every original conjunction, flow, frame and radius is retained. -/
theorem referenceFramedNormalizedEndpoint_smooth_on_same_room (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C : ℝ)
    (hData : ConformalReferenceFramedMetricData g L y0 Φ B ε C) :
    ContDiff ℝ ∞ (referenceFramedNormalizedEndpointIntegral g L Φ) ∧
      EqOn (referenceFramedNormalizedEndpoint g L Φ)
        (referenceFramedNormalizedEndpointIntegral g L Φ) (conformalReferenceFramedMetricRoom y0 ε) ∧
      ContDiffOn ℝ ∞ (referenceFramedNormalizedEndpoint g L Φ) (conformalReferenceFramedMetricRoom y0 ε) ∧
      ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ N →
        ∀ a ∈ conformalReferenceFramedMetricRoom y0 ε,
          ‖iteratedFDeriv ℝ j (referenceFramedNormalizedEndpointIntegral g L Φ) a‖ ≤ D := by
  have hEnd : ConformalReferenceGeodesicEndpointData g L y0 Φ B := hData.1
  have hsub := referenceFramedMetricRoom_subset_normalizationDomain g L y0 Φ B ε C hData
  have heq := referenceFramedNormalizedEndpoint_eqOn_integral g hg L y0 Φ B hEnd
  have hold := (contDiffOn_referenceFramedNormalizedEndpoint g hg L y0 Φ B hEnd).mono hsub
  rcases hEnd with ⟨_,_,_,_,_,_,_,hΘ,_,_,_⟩
  have hI := contDiff_referenceFramedNormalizedEndpointIntegral g hg L Φ hΘ
  refine ⟨hI,fun a ha => heq (hsub ha),hold,?_⟩
  apply exists_compact_uniform_iteratedFDeriv_bound _ hI (conformalReferenceFramedMetricRoom y0 ε)
  exact isCompact_Icc.prod
    (((isCompact_closedBall _ _).prod isCompact_Icc).prod (isCompact_closedBall _ _))

theorem exists_conformalReference_framedMetricData_smoothNormalization
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3) :
    ∃ (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C : ℝ),
      ConformalReferenceFramedMetricData g L y0 Φ B ε C ∧
      ContDiff ℝ ∞ (referenceFramedNormalizedEndpointIntegral g L Φ) ∧
      EqOn (referenceFramedNormalizedEndpoint g L Φ)
        (referenceFramedNormalizedEndpointIntegral g L Φ) (conformalReferenceFramedMetricRoom y0 ε) ∧
      ContDiffOn ℝ ∞ (referenceFramedNormalizedEndpoint g L Φ) (conformalReferenceFramedMetricRoom y0 ε) ∧
      ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ N →
        ∀ a ∈ conformalReferenceFramedMetricRoom y0 ε,
          ‖iteratedFDeriv ℝ j (referenceFramedNormalizedEndpointIntegral g L Φ) a‖ ≤ D := by
  obtain ⟨Φ,B,ε,C,hData⟩ := exists_conformalReference_framedMetricData g hg L y0
  exact ⟨Φ,B,ε,C,hData,
    referenceFramedNormalizedEndpoint_smooth_on_same_room g hg L y0 Φ B ε C hData⟩

end OAI.AnisotropicCalderon.ConnectionError
