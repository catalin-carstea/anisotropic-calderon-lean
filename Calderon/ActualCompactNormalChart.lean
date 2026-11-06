import Calderon.CompactParameterReferenceFramedNormalMetric
import Calderon.CompactZeroSliceNormTube
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

/-! UNCOMPILED author construction. The complete expansion and literal original
geometry payload were sealed before source authoring. No chart premise is added. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator NormalCoordinatesFrame

private instance instCompleteCompactNormalChartR3 : CompleteSpace R3 :=
  FiniteDimensional.complete ℝ R3

/-- Literally the entire selected metric theorem payload, at its original room radius. -/
def ConformalReferenceFramedMetricData (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C : ℝ) : Prop :=
      ConformalReferenceGeodesicEndpointData g L y0 Φ B ∧ 0 < ε ∧ 0 ≤ C ∧
      ContDiff ℝ ∞ (conformalReferenceGramFrameOperatorJoint g L) ∧
      (∀ p, Function.Bijective (conformalReferenceGramFrameOperatorJoint g L p)) ∧
      ContDiff ℝ ∞ (conformalReferenceFramedNormalMetric g L Φ) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y, ‖y-y0‖ ≤ ε → ∀ r : ℝ, |r| ≤ ε →
        ∀ z ∈ closedBall (0 : R3) 2,
          (y,r • conformalReferenceGramFrameOperatorJoint g L (q,y) z) ∈ B ∧
          (∀ t ∈ Icc (0 : ℝ) 1,
            HasDerivAt (Φ q (y,r • conformalReferenceGramFrameOperatorJoint g L (q,y) z))
              (geodesicPhaseField
                (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
                (metricOperatorField (conformalReferenceMatrix g L q))
                (Φ q (y,r • conformalReferenceGramFrameOperatorJoint g L (q,y) z) t)) t) ∧
          conformalReferenceFramedNormalMetric g L Φ (q,((y,0),z)) =
            ContinuousLinearMap.id ℝ R3 ∧
          HasDerivAt (fun s : ℝ => conformalReferenceFramedNormalMetric g L Φ (q,((y,s),z))) 0 0 ∧
          ‖conformalReferenceFramedNormalMetric g L Φ (q,((y,r),z)) -
            ContinuousLinearMap.id ℝ R3‖ ≤ C*r^2 ∧
          ‖conformalReferenceFramedNormalMetric g L Φ (q,((y,r),z)) -
            ContinuousLinearMap.id ℝ R3‖ ≤ (1/2 : ℝ) ∧
          (∀ u : R3, (1/2 : ℝ)*‖u‖^2 ≤
            inner ℝ (conformalReferenceFramedNormalMetric g L Φ (q,((y,r),z)) u) u) ∧
          ∀ u v : R3, |inner ℝ (conformalReferenceFramedNormalMetric g L Φ (q,((y,r),z)) u) v| ≤
            (3/2 : ℝ)*‖u‖*‖v‖) ∧
      ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ N →
        ∀ p ∈ conformalReferenceFramedMetricRoom y0 ε,
          ‖iteratedFDeriv ℝ j (conformalReferenceFramedNormalMetric g L Φ) p‖ ≤ D

theorem exists_conformalReference_framedMetricData
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3) :
    ∃ (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C : ℝ),
      ConformalReferenceFramedMetricData g L y0 Φ B ε C := by
  simpa only [ConformalReferenceFramedMetricData] using
    exists_compact_parameter_conformalReference_framed_normal_metric g hg L y0

@[reducible] def ReferenceEndpointVariables : Type := ℝ × ((R3 × ℝ) × R3)

/-- The physical endpoint uses precisely the parent's one chosen flow and Gram frame. -/
def referenceFramedPhysicalEndpoint (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (p : ReferenceEndpointVariables) : R3 :=
  (Φ p.1 (p.2.1.1, p.2.1.2 • conformalReferenceGramFrameOperatorJoint g L
    (p.1,p.2.1.1) p.2.2) 1).1

/-- No joint quotient extension is assumed; zero is the exact original frame slice. -/
def referenceFramedNormalizedEndpoint (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (p : ReferenceEndpointVariables) : R3 :=
  if p.2.1.2 = 0 then conformalReferenceGramFrameOperatorJoint g L (p.1,p.2.1.1) p.2.2
  else p.2.1.2⁻¹ • (referenceFramedPhysicalEndpoint g L Φ p - p.2.1.1)

/-- The normalized spatial derivative already underlying the selected framed metric. -/
def referenceFramedNormalizedJacobian (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (p : ReferenceEndpointVariables) : R3 →L[ℝ] R3 :=
  framedNormalizedEndpointDerivative (fun a => (Φ p.1 a 1).1)
    (fun y => conformalReferenceGramFrameOperatorJoint g L (p.1,y)) p.2

def referenceGramFrameInverse (g : MatrixField) (L : ℝ) (p : ℝ × R3) : R3 →L[ℝ] R3 :=
  ContinuousLinearMap.inverse (conformalReferenceGramFrameOperatorJoint g L p)

def referenceWhitenedEndpointJacobian (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (p : ReferenceEndpointVariables) : R3 →L[ℝ] R3 :=
  (referenceGramFrameInverse g L (p.1,p.2.1.1)).comp
    (referenceFramedNormalizedJacobian g L Φ p)

theorem isInvertible_compactChart_endomorphism (A : R3 →L[ℝ] R3)
    (hA : Function.Injective A) : A.IsInvertible := by
  have hb : Function.Bijective A.toLinearMap :=
    ⟨hA,A.toLinearMap.surjective_of_injective hA⟩
  refine ⟨(LinearEquiv.ofBijective A.toLinearMap hb).toContinuousLinearEquiv,?_⟩
  ext u
  rfl

theorem referenceGramFrame_isInvertible (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (p : ℝ × R3) : (conformalReferenceGramFrameOperatorJoint g L p).IsInvertible :=
  isInvertible_compactChart_endomorphism _
    (conformalReferenceGramFrameOperatorJoint_bijective g hg L p).1

theorem contDiff_referenceGramFrameInverse (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) : ContDiff ℝ ∞ (referenceGramFrameInverse g L) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (referenceGramFrame_isInvertible g hg L p).contDiffAt_map_inverse.comp p
    (contDiff_conformalReferenceGramFrameOperatorJoint g hg L).contDiffAt

theorem referenceFramedNormalizedJacobian_eq_joint (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1))
    (p : ReferenceEndpointVariables) :
    referenceFramedNormalizedJacobian g L Φ p =
      ((parameterPhaseDerivative (fun a : ℝ × (R3 × R3) => (Φ a.1 a.2 1).1)
        (p.1,(p.2.1.1,p.2.1.2 • conformalReferenceGramFrameOperatorJoint g L
          (p.1,p.2.1.1) p.2.2))).comp (ContinuousLinearMap.inr ℝ R3 R3)).comp
            (conformalReferenceGramFrameOperatorJoint g L (p.1,p.2.1.1)) := by
  unfold referenceFramedNormalizedJacobian framedNormalizedEndpointDerivative
    normalizedEndpointDerivative framedEndpointParameter
  rw [fderiv_parameter_endpoint_slice (fun a : ℝ × (R3 × R3) => (Φ a.1 a.2 1).1) hΘ]

theorem contDiff_referenceFramedPhysicalEndpoint (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1)) :
    ContDiff ℝ ∞ (referenceFramedPhysicalEndpoint g L Φ) := by
  let A : ReferenceEndpointVariables → R3 →L[ℝ] R3 := fun p =>
    conformalReferenceGramFrameOperatorJoint g L (p.1,p.2.1.1)
  have hA : ContDiff ℝ ∞ A :=
    (contDiff_conformalReferenceGramFrameOperatorJoint g hg L).comp
      (contDiff_fst.prodMk contDiff_snd.fst.fst)
  exact hΘ.comp (contDiff_fst.prodMk
    (contDiff_snd.fst.fst.prodMk (contDiff_snd.fst.snd.smul (hA.clm_apply contDiff_snd.snd))))

theorem contDiff_referenceFramedNormalizedJacobian (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1)) :
    ContDiff ℝ ∞ (referenceFramedNormalizedJacobian g L Φ) := by
  let A : ReferenceEndpointVariables → R3 →L[ℝ] R3 := fun p =>
    conformalReferenceGramFrameOperatorJoint g L (p.1,p.2.1.1)
  let T : ReferenceEndpointVariables → ℝ × (R3 × R3) := fun p =>
    (p.1,(p.2.1.1,p.2.1.2 • A p p.2.2))
  have hA : ContDiff ℝ ∞ A :=
    (contDiff_conformalReferenceGramFrameOperatorJoint g hg L).comp
      (contDiff_fst.prodMk contDiff_snd.fst.fst)
  have hT : ContDiff ℝ ∞ T := contDiff_fst.prodMk
    (contDiff_snd.fst.fst.prodMk (contDiff_snd.fst.snd.smul (hA.clm_apply contDiff_snd.snd)))
  have hJ : ContDiff ℝ ∞ (fun p : ReferenceEndpointVariables =>
      ((parameterPhaseDerivative (fun a : ℝ × (R3 × R3) => (Φ a.1 a.2 1).1)
        (T p)).comp (ContinuousLinearMap.inr ℝ R3 R3)).comp (A p)) :=
    (((contDiff_parameterPhaseDerivative _ hΘ).comp hT).clm_comp contDiff_const).clm_comp hA
  have heq : referenceFramedNormalizedJacobian g L Φ =
      fun p : ReferenceEndpointVariables =>
        ((parameterPhaseDerivative (fun a : ℝ × (R3 × R3) => (Φ a.1 a.2 1).1)
          (T p)).comp (ContinuousLinearMap.inr ℝ R3 R3)).comp (A p) :=
    funext (referenceFramedNormalizedJacobian_eq_joint g L Φ hΘ)
  rw [heq]
  exact hJ

theorem contDiff_referenceWhitenedEndpointJacobian (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1)) :
    ContDiff ℝ ∞ (referenceWhitenedEndpointJacobian g L Φ) :=
  ((contDiff_referenceGramFrameInverse g hg L).comp
    (contDiff_fst.prodMk contDiff_snd.fst.fst)).clm_comp
      (contDiff_referenceFramedNormalizedJacobian g hg L Φ hΘ)

theorem referenceFramedNormalizedJacobian_zero (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (q : ℝ) (c z : R3)
    (hfirst : HasFDerivAt (fun a => (Φ q a 1).1)
      (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (c,0)) :
    referenceFramedNormalizedJacobian g L Φ (q,((c,0),z)) =
      conformalReferenceGramFrameOperatorJoint g L (q,c) := by
  unfold referenceFramedNormalizedJacobian framedNormalizedEndpointDerivative framedEndpointParameter
  rw [normalizedEndpointDerivative_zero _ c _ hfirst,ContinuousLinearMap.id_comp]

theorem referenceFramedNormalizedEndpoint_zero (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (q : ℝ) (c z : R3) :
    referenceFramedNormalizedEndpoint g L Φ (q,((c,0),z)) =
      conformalReferenceGramFrameOperatorJoint g L (q,c) z := by
  simp only [referenceFramedNormalizedEndpoint,ite_true]

theorem hasFDerivAt_referenceFramedNormalizedEndpoint_slice (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (q : ℝ) (c z : R3) (r : ℝ)
    (hΘq : ContDiff ℝ ∞ (fun a => (Φ q a 1).1))
    (hfirst : HasFDerivAt (fun a => (Φ q a 1).1)
      (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (c,0)) :
    HasFDerivAt (fun w => referenceFramedNormalizedEndpoint g L Φ (q,((c,r),w)))
      (referenceFramedNormalizedJacobian g L Φ (q,((c,r),z))) z := by
  by_cases hr : r = 0
  · subst r
    rw [referenceFramedNormalizedJacobian_zero g L Φ q c z hfirst]
    simpa only [referenceFramedNormalizedEndpoint_zero] using
      (conformalReferenceGramFrameOperatorJoint g L (q,c)).hasFDerivAt (x := z)
  · have hd := hasFDerivAt_framedScaledEndpoint_slice (fun a => (Φ q a 1).1)
      (fun y => conformalReferenceGramFrameOperatorJoint g L (q,y)) hΘq c z r
    have hn := (hd.sub (hasFDerivAt_const c z)).const_smul r⁻¹
    simpa only [referenceFramedNormalizedEndpoint,hr,ite_false,referenceFramedPhysicalEndpoint,
      referenceFramedNormalizedJacobian,Pi.smul_def,Pi.sub_def,Pi.smul_apply,Pi.sub_apply,Function.comp_apply,
      sub_zero,smul_smul,inv_mul_cancel₀ hr,one_smul] using hn

theorem contDiff_referenceFramedNormalizedEndpoint_slice (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (q : ℝ) (c : R3) (r : ℝ)
    (hΘq : ContDiff ℝ ∞ (fun a => (Φ q a 1).1)) :
    ContDiff ℝ ∞ (fun z => referenceFramedNormalizedEndpoint g L Φ (q,((c,r),z))) := by
  by_cases hr : r = 0
  · subst r
    simpa only [referenceFramedNormalizedEndpoint_zero] using
      (conformalReferenceGramFrameOperatorJoint g L (q,c)).contDiff
  · have hp : ContDiff ℝ ∞ (fun z : R3 => referenceFramedPhysicalEndpoint g L Φ (q,((c,r),z))) :=
      hΘq.comp (contDiff_const.prodMk
        ((conformalReferenceGramFrameOperatorJoint g L (q,c)).contDiff.const_smul r))
    simpa only [referenceFramedNormalizedEndpoint,hr,ite_false] using
      (hp.sub contDiff_const).const_smul r⁻¹

theorem referenceFramedPhysicalEndpoint_eq_center_add_radius_normalized (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (q : ℝ) (c z : R3) (r : ℝ)
    (hzero : (Φ q (c,0) 1).1 = c) :
    referenceFramedPhysicalEndpoint g L Φ (q,((c,r),z)) =
      c + r • referenceFramedNormalizedEndpoint g L Φ (q,((c,r),z)) := by
  by_cases hr : r = 0
  · subst r
    simp only [referenceFramedPhysicalEndpoint,zero_smul,hzero,add_zero]
  · rw [referenceFramedNormalizedEndpoint,if_neg hr,smul_smul,mul_inv_cancel₀ hr,one_smul]
    abel

/-- The only radius choice is a compact tube around the exact zero Jacobian slice. -/
theorem exists_signed_radius_of_compact_identity_slice
    (Q : ReferenceEndpointVariables → R3 →L[ℝ] R3) (hQ : Continuous Q)
    (y0 : R3) (ε : ℝ) (hε : 0 < ε)
    (hzero : ∀ q ∈ Icc (0 : ℝ) 1, ∀ c, ‖c-y0‖ ≤ ε →
      ∀ z ∈ closedBall (0 : R3) 2, Q (q,((c,0),z)) = ContinuousLinearMap.id ℝ R3) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ c, ‖c-y0‖ ≤ ε →
      ∀ r : ℝ, |r| ≤ δ → ∀ z ∈ closedBall (0 : R3) 2,
        ‖Q (q,((c,r),z)) - ContinuousLinearMap.id ℝ R3‖ < (1/2 : ℝ) := by
  let K : Set (ℝ × (R3 × R3)) :=
    Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ε ×ˢ closedBall (0 : R3) 2)
  have hK : IsCompact K := isCompact_Icc.prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  let H : (ℝ × (R3 × R3)) × ℝ → R3 →L[ℝ] R3 :=
    fun p => Q (p.1.1,((p.1.2.1,p.2),p.1.2.2)) - ContinuousLinearMap.id ℝ R3
  have hH : Continuous H := (hQ.comp
    (continuous_fst.fst.prodMk
      ((continuous_fst.snd.fst.prodMk continuous_snd).prodMk continuous_fst.snd.snd))).sub
        continuous_const
  have hH0 : ∀ p ∈ K, H (p,0) = 0 := by
    intro p hp
    have hc : ‖p.2.1-y0‖ ≤ ε := by
      simpa only [mem_closedBall,dist_eq_norm] using hp.2.1
    change Q (p.1,((p.2.1,0),p.2.2)) - ContinuousLinearMap.id ℝ R3 = 0
    rw [hzero p.1 hp.1 p.2.1 hc p.2.2 hp.2.2,sub_self]
  obtain ⟨δ,hδ,hδε,hbound⟩ := exists_signed_radius_of_compact_zero_slice
    H hH K hK ε hε (1/2 : ℝ) (half_pos zero_lt_one) hH0
  refine ⟨δ,hδ,hδε,?_⟩
  intro q hq c hc r hr z hz
  have hp : (q,(c,z)) ∈ K :=
    ⟨hq,by simpa only [mem_closedBall,dist_eq_norm] using hc,hz⟩
  exact hbound (q,(c,z)) hp r hr

theorem norm_lower_bound_of_derivative_near_id_closedBall
    (f : R3 → R3) (J : R3 → R3 →L[ℝ] R3)
    (hf : ∀ z ∈ closedBall (0 : R3) 2, HasFDerivAt f (J z) z)
    (hJ : ∀ z ∈ closedBall (0 : R3) 2, ‖J z - ContinuousLinearMap.id ℝ R3‖ ≤ (1/2 : ℝ))
    (x : R3) (hx : x ∈ closedBall (0 : R3) 2) (y : R3) (hy : y ∈ closedBall (0 : R3) 2) :
    (1/2 : ℝ)*‖y-x‖ ≤ ‖f y-f x‖ := by
  have hm : ‖f y-f x-(y-x)‖ ≤ (1/2 : ℝ)*‖y-x‖ := by
    simpa only [ContinuousLinearMap.id_apply] using
      (Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (𝕜 := ℝ)
        (f := f) (f' := J) (φ := ContinuousLinearMap.id ℝ R3) (C := (1/2 : ℝ))
        (fun z hz => (hf z hz).hasFDerivWithinAt) hJ (convex_closedBall _ _) hx hy)
  have ht : ‖y-x‖ ≤ ‖f y-f x‖ + ‖f y-f x-(y-x)‖ := by
    calc
      ‖y-x‖ = ‖(f y-f x) + ((y-x)-(f y-f x))‖ := by congr 1; abel
      _ ≤ ‖f y-f x‖ + ‖(y-x)-(f y-f x)‖ := norm_add_le _ _
      _ = ‖f y-f x‖ + ‖f y-f x-(y-x)‖ := by rw [norm_sub_rev (y-x) (f y-f x)]
  linarith

theorem injective_operator_of_norm_sub_id_half (Q : R3 →L[ℝ] R3)
    (hQ : ‖Q - ContinuousLinearMap.id ℝ R3‖ ≤ (1/2 : ℝ)) : Function.Injective Q := by
  intro x y hxy
  have hb := (Q-ContinuousLinearMap.id ℝ R3).le_opNorm (x-y)
  have hm := mul_le_mul_of_nonneg_right hQ (norm_nonneg (x-y))
  have hzero : Q (x-y) = 0 := by rw [map_sub,hxy,sub_self]
  have h : ‖x-y‖ ≤ (1/2 : ℝ)*‖x-y‖ := by
    simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,hzero,
      zero_sub,norm_neg] using hb.trans hm
  have hz : ‖x-y‖ = 0 := by linarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Whole-ball injection and native local openness give the exact whole-ball chart. -/
theorem exists_openBall_chart_of_injOn_and_invertible_derivative
    (f : R3 → R3) (hf : ContDiff ℝ ∞ f)
    (hi : InjOn f (closedBall (0 : R3) 2))
    (hD : ∀ z ∈ ball (0 : R3) 2, (fderiv ℝ f z).IsInvertible) :
    ∃ e : OpenPartialHomeomorph R3 R3,
      (e : R3 → R3) = f ∧ e.source = ball (0 : R3) 2 ∧ e.target = f '' ball (0 : R3) 2 ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ z ∈ ball (0 : R3) 2, e.symm (f z) = z) ∧ ∀ y ∈ e.target, f (e.symm y) = y := by
  let U : Set R3 := ball (0 : R3) 2
  have hiU : InjOn f U := hi.mono ball_subset_closedBall
  have hU : IsOpen U := isOpen_ball
  have ho : IsOpenMap (U.domRestrict f) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro x
    obtain ⟨D,hDeq⟩ := hD x x.property
    have hfd : HasFDerivAt f (D : R3 →L[ℝ] R3) (x : R3) := by
      rw [hDeq]
      exact (hf.differentiable (by simp) (x : R3)).hasFDerivAt
    have hmap : Filter.map f (𝓝 (x : R3)) = 𝓝 (f (x : R3)) :=
      (hf.contDiffAt.hasStrictFDerivAt' hfd (by simp)).map_nhds_eq_of_equiv
    have hsub : Filter.map ((↑) : U → R3) (𝓝 x) = 𝓝 (x : R3) :=
      map_nhds_subtype_coe_eq_nhds x.property (hU.mem_nhds x.property)
    change 𝓝 (f (x : R3)) ≤ Filter.map (f ∘ ((↑) : U → R3)) (𝓝 x)
    rw [← Filter.map_map,hsub,hmap]
  let pe : PartialEquiv R3 R3 := hiU.toPartialEquiv f U
  let e : OpenPartialHomeomorph R3 R3 :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict pe hf.continuous.continuousOn ho hU
  have heq : (e : R3 → R3) = f := rfl
  have hs : e.source = U := rfl
  have ht : e.target = f '' U := rfl
  refine ⟨e,heq,hs,ht,?_,?_,?_⟩
  · intro y hy
    have hx : e.symm y ∈ U := by simpa only [hs] using e.map_target hy
    obtain ⟨D,hDeq⟩ := hD (e.symm y) hx
    have hfd : HasFDerivAt e (D : R3 →L[ℝ] R3) (e.symm y) := by
      change HasFDerivAt f (D : R3 →L[ℝ] R3) (e.symm y)
      rw [hDeq]
      exact (hf.differentiable (by simp) (e.symm y)).hasFDerivAt
    exact (e.contDiffAt_symm hy hfd hf.contDiffAt).contDiffWithinAt
  · intro z hz
    have hzsource : z ∈ e.source := by simpa only [hs] using hz
    exact e.left_inv hzsource
  · intro y hy
    exact e.right_inv hy

theorem contDiffOn_inverse_referencePhysicalJacobian (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
    (hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1)) :
    ContDiffOn ℝ ∞ (fun p : ReferenceEndpointVariables =>
      ContinuousLinearMap.inverse (p.2.1.2 • referenceFramedNormalizedJacobian g L Φ p))
      {p | (p.2.1.2 • referenceFramedNormalizedJacobian g L Φ p).IsInvertible} := by
  have hS : ContDiff ℝ ∞ (fun p : ReferenceEndpointVariables =>
      p.2.1.2 • referenceFramedNormalizedJacobian g L Φ p) :=
    contDiff_snd.fst.snd.smul (contDiff_referenceFramedNormalizedJacobian g hg L Φ hΘ)
  intro p hp
  exact (hp.contDiffAt_map_inverse.comp p hS.contDiffAt).contDiffWithinAt

/-- One original flow and full metric payload, strengthened by a compact signed whole-ball chart. -/
theorem exists_compact_conformalReference_wholeBall_normal_chart
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3) :
    ∃ (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C δ : ℝ),
      ConformalReferenceFramedMetricData g L y0 Φ B ε C ∧ 0 < δ ∧ δ ≤ ε ∧
      ContDiff ℝ ∞ (referenceFramedPhysicalEndpoint g L Φ) ∧
      ContDiff ℝ ∞ (referenceFramedNormalizedJacobian g L Φ) ∧
      ContDiff ℝ ∞ (referenceWhitenedEndpointJacobian g L Φ) ∧
      ContDiffOn ℝ ∞ (fun p : ReferenceEndpointVariables =>
        ContinuousLinearMap.inverse (p.2.1.2 • referenceFramedNormalizedJacobian g L Φ p))
        {p | (p.2.1.2 • referenceFramedNormalizedJacobian g L Φ p).IsInvertible} ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ c, ‖c-y0‖ ≤ ε → ∀ r : ℝ, |r| ≤ δ →
        (∀ z ∈ closedBall (0 : R3) 2,
          ‖referenceWhitenedEndpointJacobian g L Φ (q,((c,r),z)) -
            ContinuousLinearMap.id ℝ R3‖ < (1/2 : ℝ)) ∧
        (∀ z, referenceFramedNormalizedJacobian g L Φ (q,((c,0),z)) =
          conformalReferenceGramFrameOperatorJoint g L (q,c)) ∧
        ContDiff ℝ ∞ (fun z => referenceFramedNormalizedEndpoint g L Φ (q,((c,r),z))) ∧
        (∀ z, HasFDerivAt (fun w => referenceFramedNormalizedEndpoint g L Φ (q,((c,r),w)))
          (referenceFramedNormalizedJacobian g L Φ (q,((c,r),z))) z) ∧
        (∀ z, referenceFramedPhysicalEndpoint g L Φ (q,((c,r),z)) =
          c + r • referenceFramedNormalizedEndpoint g L Φ (q,((c,r),z))) ∧
        (∀ x ∈ closedBall (0 : R3) 2, ∀ y ∈ closedBall (0 : R3) 2,
          (1/2 : ℝ)*‖y-x‖ ≤ ‖referenceGramFrameInverse g L (q,c)
            (referenceFramedNormalizedEndpoint g L Φ (q,((c,r),y)) -
              referenceFramedNormalizedEndpoint g L Φ (q,((c,r),x)))‖) ∧
        InjOn (fun z => referenceFramedNormalizedEndpoint g L Φ (q,((c,r),z)))
          (closedBall (0 : R3) 2) ∧
        (r ≠ 0 →
          (∀ x ∈ closedBall (0 : R3) 2, ∀ y ∈ closedBall (0 : R3) 2,
            (|r|/2)*‖y-x‖ ≤ ‖referenceGramFrameInverse g L (q,c)
              (referenceFramedPhysicalEndpoint g L Φ (q,((c,r),y)) -
                referenceFramedPhysicalEndpoint g L Φ (q,((c,r),x)))‖) ∧
          InjOn (fun z => referenceFramedPhysicalEndpoint g L Φ (q,((c,r),z)))
            (closedBall (0 : R3) 2) ∧
          ∃ e : OpenPartialHomeomorph R3 R3,
            (e : R3 → R3) = (fun z => referenceFramedPhysicalEndpoint g L Φ (q,((c,r),z))) ∧
            e.source = ball (0 : R3) 2 ∧
            e.target = (fun z => referenceFramedPhysicalEndpoint g L Φ (q,((c,r),z))) ''
              ball (0 : R3) 2 ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
            (∀ z ∈ ball (0 : R3) 2,
              e.symm (referenceFramedPhysicalEndpoint g L Φ (q,((c,r),z))) = z) ∧
            (∀ y ∈ e.target, referenceFramedPhysicalEndpoint g L Φ (q,((c,r),e.symm y)) = y) ∧
            ∀ y ∈ e.target, referenceFramedNormalizedEndpoint g L Φ (q,((c,r),e.symm y)) =
              r⁻¹ • (y-c)) := by
  obtain ⟨Φ,B,ε,C,hData⟩ := exists_conformalReference_framedMetricData g hg L y0
  have hSaved := hData
  rcases hData with ⟨hEndpoint,hε,hC,hF,hFbij,hG,hroom,hjets⟩
  rcases hEndpoint with ⟨hB,hy0,hΦ,hinit,hadd,hstat,hODE,hΘ,hvalue,hfirst,hsecond⟩
  have hcB (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (c : R3) (hc : ‖c-y0‖ ≤ ε) :
      (c,0) ∈ B := by
    have h := (hroom q hq c hc 0 (by simpa using hε.le) 0 (by simp)).1
    simpa only [zero_smul] using h
  have hQzero : ∀ q ∈ Icc (0 : ℝ) 1, ∀ c, ‖c-y0‖ ≤ ε →
      ∀ z ∈ closedBall (0 : R3) 2,
        referenceWhitenedEndpointJacobian g L Φ (q,((c,0),z)) = ContinuousLinearMap.id ℝ R3 := by
    intro q hq c hc z hz
    unfold referenceWhitenedEndpointJacobian referenceGramFrameInverse
    rw [referenceFramedNormalizedJacobian_zero g L Φ q c z (hfirst q hq c (hcB q hq c hc))]
    exact (referenceGramFrame_isInvertible g hg L (q,c)).inverse_comp_self
  obtain ⟨δ,hδ,hδε,hbound⟩ := exists_signed_radius_of_compact_identity_slice
    (referenceWhitenedEndpointJacobian g L Φ)
    (contDiff_referenceWhitenedEndpointJacobian g hg L Φ hΘ).continuous y0 ε hε hQzero
  refine ⟨Φ,B,ε,C,δ,hSaved,hδ,hδε,
    contDiff_referenceFramedPhysicalEndpoint g hg L Φ hΘ,
    contDiff_referenceFramedNormalizedJacobian g hg L Φ hΘ,
    contDiff_referenceWhitenedEndpointJacobian g hg L Φ hΘ,
    contDiffOn_inverse_referencePhysicalJacobian g hg L Φ hΘ,?_⟩
  intro q hq c hc r hr
  have hfirstc := hfirst q hq c (hcB q hq c hc)
  have hzeroc := hvalue q hq c (hcB q hq c hc)
  have hΘq : ContDiff ℝ ∞ (fun a => (Φ q a 1).1) :=
    hΘ.comp (contDiff_const.prodMk contDiff_id)
  let E : R3 → R3 := fun z => referenceFramedNormalizedEndpoint g L Φ (q,((c,r),z))
  let P : R3 → R3 := fun z => referenceFramedPhysicalEndpoint g L Φ (q,((c,r),z))
  let A : R3 →L[ℝ] R3 := referenceGramFrameInverse g L (q,c)
  let J : R3 → R3 →L[ℝ] R3 := fun z => referenceFramedNormalizedJacobian g L Φ (q,((c,r),z))
  let Q : R3 → R3 →L[ℝ] R3 := fun z => referenceWhitenedEndpointJacobian g L Φ (q,((c,r),z))
  have hEder (z : R3) : HasFDerivAt E (J z) z :=
    hasFDerivAt_referenceFramedNormalizedEndpoint_slice g L Φ q c z r hΘq hfirstc
  have hWder (z : R3) : HasFDerivAt (fun w => A (E w)) (Q z) z :=
    (A.hasFDerivAt (x := E z)).comp z (hEder z)
  have hlip (x : R3) (hx : x ∈ closedBall (0 : R3) 2)
      (y : R3) (hy : y ∈ closedBall (0 : R3) 2) :
      (1/2 : ℝ)*‖y-x‖ ≤ ‖A (E y-E x)‖ := by
    simpa only [map_sub] using norm_lower_bound_of_derivative_near_id_closedBall
      (fun w => A (E w)) Q (fun z _ => hWder z)
      (fun z hz => (hbound q hq c hc r hr z hz).le) x hx y hy
  have hiE : InjOn E (closedBall (0 : R3) 2) := by
    intro x hx y hy hxy
    have h := hlip x hx y hy
    simp only [hxy,sub_self,map_zero,norm_zero] at h
    have hz : ‖y-x‖ = 0 := by linarith [norm_nonneg (y-x)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  have hfactor (z : R3) : P z = c + r • E z :=
    referenceFramedPhysicalEndpoint_eq_center_add_radius_normalized g L Φ q c z r hzeroc
  refine ⟨hbound q hq c hc r hr,
    fun z => referenceFramedNormalizedJacobian_zero g L Φ q c z hfirstc,
    contDiff_referenceFramedNormalizedEndpoint_slice g L Φ q c r hΘq,hEder,hfactor,hlip,hiE,?_⟩
  intro hne
  have hiP : InjOn P (closedBall (0 : R3) 2) := by
    intro x hx y hy hxy
    apply hiE hx hy
    simp only [E,referenceFramedNormalizedEndpoint,hne,ite_false]
    exact congrArg (fun w : R3 => r⁻¹ • (w-c)) hxy
  have hPdiff (x y : R3) : A (P y-P x) = r • A (E y-E x) := by
    rw [hfactor y,hfactor x]
    have heq : (c+r • E y)-(c+r • E x) = r • (E y-E x) := by rw [smul_sub]; abel
    rw [heq,map_smul]
  have hphyslip (x : R3) (hx : x ∈ closedBall (0 : R3) 2)
      (y : R3) (hy : y ∈ closedBall (0 : R3) 2) :
      (|r|/2)*‖y-x‖ ≤ ‖A (P y-P x)‖ := by
    rw [hPdiff,norm_smul,Real.norm_eq_abs]
    have h := mul_le_mul_of_nonneg_left (hlip x hx y hy) (abs_nonneg r)
    convert h using 1 <;> ring
  have hP : ContDiff ℝ ∞ P :=
    (contDiff_referenceFramedPhysicalEndpoint g hg L Φ hΘ).comp
      (contDiff_const.prodMk ((contDiff_const.prodMk contDiff_const).prodMk contDiff_id))
  have hPD (z : R3) (hz : z ∈ ball (0 : R3) 2) : (fderiv ℝ P z).IsInvertible := by
    have hQi : Function.Injective (Q z) := injective_operator_of_norm_sub_id_half _
      (hbound q hq c hc r hr z (ball_subset_closedBall hz)).le
    have hJi : Function.Injective (J z) := by
      intro u v huv
      apply hQi
      exact congrArg A huv
    have hri : Function.Injective (r • J z) := by
      intro u v huv
      apply hJi
      have hcancel := congrArg (fun w : R3 => r⁻¹ • w) huv
      simpa only [ContinuousLinearMap.smul_apply,smul_smul,inv_mul_cancel₀ hne,one_smul] using hcancel
    have hd : HasFDerivAt P (r • J z) z :=
      hasFDerivAt_framedScaledEndpoint_slice (fun a => (Φ q a 1).1)
        (fun y => conformalReferenceGramFrameOperatorJoint g L (q,y)) hΘq c z r
    rw [hd.fderiv]
    exact isInvertible_compactChart_endomorphism _ hri
  obtain ⟨e,he,hs,ht,hsi,hleft,hright⟩ :=
    exists_openBall_chart_of_injOn_and_invertible_derivative P hP hiP hPD
  refine ⟨hphyslip,hiP,e,he,hs,ht,hsi,hleft,hright,?_⟩
  intro y hy
  simp only [referenceFramedNormalizedEndpoint,hne,ite_false]
  change r⁻¹ • (P (e.symm y)-c) = r⁻¹ • (y-c)
  rw [hright y hy]

end OAI.AnisotropicCalderon.ConnectionError
