import Calderon.MixedKernelConstruction.MixedKernelNormalizedSeparatingJets
import Calderon.SmoothReferenceFramedNormalizedEndpoint
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError
open scoped ContDiff InnerProductSpace Topology

/-- Both bounds for the ACTUAL Gram frame on a compact parameter set, derived from its smooth inverse. -/
theorem exists_compact_native_frame_bounds (S : KnownSideSourceData) (L : ℝ)
    (K : Set (ℝ × R3)) (hK : IsCompact K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ a ∈ K, ∀ z : R3, ‖z‖ = 1 →
      c ≤ ‖conformalReferenceGramFrameOperatorJoint S.g1 L a z‖ ∧
      ‖conformalReferenceGramFrameOperatorJoint S.g1 L a z‖ ≤ C := by
  let F := conformalReferenceGramFrameOperatorJoint S.g1 L
  let Q := referenceGramFrameInverse S.g1 L
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn
    (contDiff_conformalReferenceGramFrameOperatorJoint S.g1 S.g1_admissible L).continuous.continuousOn
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (contDiff_referenceGramFrameInverse S.g1 S.g1_admissible L).continuous.continuousOn
  let D : ℝ := |B|+1
  have hD : 0 < D := by dsimp [D];positivity
  refine ⟨1/D,|A|+1,div_pos (by norm_num) hD,by positivity,?_⟩
  intro a ha z hz
  have hi : Q a (F a z) = z := by
    have hh := congrArg (fun T : R3 →L[ℝ] R3 => T z)
      (referenceGramFrame_isInvertible S.g1 S.g1_admissible L a).inverse_comp_self
    simpa only [Q,F,referenceGramFrameInverse,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hh
  have hQ : ‖Q a‖ ≤ D := (hB a ha).trans ((le_abs_self B).trans (by dsimp [D];linarith))
  have hF : ‖F a‖ ≤ |A|+1 := (hA a ha).trans ((le_abs_self A).trans (by linarith))
  have hlow : 1 ≤ D*‖F a z‖ := by
    have hh := (Q a).le_opNorm (F a z)
    rw [hi,hz] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hQ (norm_nonneg _))
  refine ⟨(div_le_iff₀ hD).mpr (by nlinarith),?_⟩
  have hh := (F a).le_opNorm z
  rw [hz,mul_one] at hh
  exact hh.trans hF

/-- The actual normalization holds on the entire CLOSED center ball inherited from the same packet room. -/
theorem packet_normalizedEndpoint_zero_closed_centers (S : KnownSideSourceData) (L : ℝ)
    (P : NativeNormalPacket S L) (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-P.y0‖ ≤ 4*P.rho) (z : R3) :
    referenceFramedNormalizedEndpointIntegral S.g1 L P.Phi (lam,((y,0),z)) =
      conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y) z := by
  have hNormal := P.native_data.1.1
  rcases hNormal with ⟨hEnd,heps,_,_,_,_,hRoom,_⟩
  have hsmall : 4*P.rho ≤ P.epsGeo := P.native_data.1.2.2.1
  have hB : (y,0) ∈ P.B := by
    have hh := (hRoom lam hlam y (hy.trans hsmall) 0 (by simpa using heps.le)
      0 (by simp)).1
    simpa only [zero_smul] using hh
  rcases hEnd with ⟨_,_,_,_,_,_,_,hTheta,hvalue,hfirst,_⟩
  rw [referenceFramedNormalizedEndpointIntegral_eq S.g1 S.g1_admissible L P.Phi hTheta
    lam y z 0 (hvalue lam hlam y hB) (hfirst lam hlam y hB)]
  exact referenceFramedNormalizedEndpoint_zero S.g1 L P.Phi lam y z

/-- Positive physical separation and an upper displacement bound, uniform BEFORE the arbitrary radius data. -/
theorem exists_packet_endpoint_linear_bounds (S : KnownSideSourceData) (L : ℝ)
    (P : NativeNormalPacket S L) :
    ∃ r0 c C : ℝ, 0 < r0 ∧ r0 ≤ 4*P.rho ∧ r0 ≤ 1 ∧ 0 < c ∧ 0 < C ∧
      ∀ lam ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-P.y0‖ ≤ 4*P.rho →
        ∀ r ∈ Icc (0 : ℝ) r0, ∀ z : R3, ‖z‖ = 1 →
          c*r ≤ ‖packetEndpoint S L P lam y r z-y‖ ∧
          ‖packetEndpoint S L P lam y r z-y‖ ≤ C*r := by
  let K0 : Set (ℝ × R3) := Icc (0 : ℝ) 1 ×ˢ closedBall P.y0 (4*P.rho)
  let K : Set ((ℝ × R3) × R3) := K0 ×ˢ sphere (0 : R3) 1
  have hK0 : IsCompact K0 := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hK : IsCompact K := hK0.prod (isCompact_sphere _ _)
  obtain ⟨a,A,ha,hA,Hframe⟩ := exists_compact_native_frame_bounds S L K0 hK0
  let F : ℝ × ((ℝ × R3) × R3) → R3 := fun b =>
    referenceFramedNormalizedEndpointIntegral S.g1 L P.Phi
      (b.2.1.1,((b.2.1.2,b.1),b.2.2)) -
        conformalReferenceGramFrameOperatorJoint S.g1 L b.2.1 b.2.2
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun b : ℝ × (R3 × R3) => (P.Phi b.1 b.2 1).1) :=
    hEnd.2.2.2.2.2.2.2.1
  have hFc : Continuous F := by
    have hi := (contDiff_referenceFramedNormalizedEndpointIntegral S.g1 S.g1_admissible L P.Phi hTheta).continuous
    have hf := (contDiff_conformalReferenceGramFrameOperatorJoint S.g1 S.g1_admissible L).continuous
    dsimp [F]
    fun_prop
  have hzero : ∀ b ∈ K, F (0,b) = 0 := by
    intro b hb
    have hy : ‖b.1.2-P.y0‖ ≤ 4*P.rho := by
      simpa only [mem_closedBall,dist_eq_norm] using hb.1.2
    dsimp [F]
    rw [packet_normalizedEndpoint_zero_closed_centers S L P b.1.1 hb.1.1 b.1.2 hy b.2,sub_self]
  obtain ⟨d,hd,Hd⟩ := exists_uniform_parameter_error_on_compact K hK F 0
    (fun b hb => hFc.continuousAt) hzero (a/2) (half_pos ha)
  let r0 := min (4*P.rho) (min d 1)
  have hr0 : 0 < r0 := lt_min (by positivity [P.rho_positive]) (lt_min hd (by norm_num))
  have hr0rho : r0 ≤ 4*P.rho := min_le_left _ _
  have hr0d : r0 ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hr01 : r0 ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r0,a/2,A+a/2,hr0,hr0rho,hr01,half_pos ha,by positivity,?_⟩
  intro lam hlam y hy r hr z hz
  have hb0 : (lam,y) ∈ K0 := ⟨hlam,by simpa only [mem_closedBall,dist_eq_norm] using hy⟩
  have hb : ((lam,y),z) ∈ K := ⟨hb0,by simpa only [mem_sphere,dist_zero_right] using hz⟩
  let E := referenceFramedNormalizedEndpointIntegral S.g1 L P.Phi (lam,((y,r),z))
  let V := conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y) z
  have he : ‖E-V‖ < a/2 := by
    simpa only [F,sub_zero] using Hd r ⟨hr.1,hr.2.trans hr0d⟩ ((lam,y),z) hb
  have hfv := Hframe (lam,y) hb0 z hz
  have hlow : a/2 ≤ ‖E‖ := by
    have hh := norm_sub_le E (E-V)
    rw [sub_sub_cancel] at hh
    nlinarith [hfv.1]
  have hhigh : ‖E‖ ≤ A+a/2 := by
    have hh := norm_add_le (E-V) V
    rw [sub_add_cancel] at hh
    linarith [hfv.2]
  have hNormal := P.native_data.1.1
  rcases hNormal with ⟨_,heps,_,_,_,_,hRoom,_⟩
  have hsmall : 4*P.rho ≤ P.epsGeo := P.native_data.1.2.2.1
  have hB : (y,0) ∈ P.B := by
    have hh := (hRoom lam hlam y (hy.trans hsmall) 0 (by simpa using heps.le) 0 (by simp)).1
    simpa only [zero_smul] using hh
  have hphys := referenceFramedPhysicalEndpoint_eq_center_add_radius_integral_on_domain
    S.g1 S.g1_admissible L P.y0 P.Phi P.B hEnd (lam,((y,r),z)) ⟨hlam,hB⟩
  have hnorm : ‖packetEndpoint S L P lam y r z-y‖ = r*‖E‖ := by
    change ‖referenceFramedPhysicalEndpoint S.g1 L P.Phi (lam,((y,r),z))-y‖ = _
    rw [hphys,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr.1]
  rw [hnorm]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlow hr.1]
  · nlinarith [mul_le_mul_of_nonneg_left hhigh hr.1]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
