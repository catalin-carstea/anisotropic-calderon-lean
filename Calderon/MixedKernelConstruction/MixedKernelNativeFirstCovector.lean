import Calderon.MixedKernelConstruction.MixedKernelImplicitSphereFirstJet
import Calderon.ActualPhysicalPullbackMetric
import Mathlib.Analysis.InnerProductSpace.Calculus
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff InnerProductSpace Topology

/-- Differentiating the exact native sphere identity determines the first covector. -/
theorem first_partial_formula_of_normalized_sphere_identity
    (rho : R3 × R3 → ℝ) (E : R3 → R3) (r : ℝ) (J : R3 →L[ℝ] R3)
    (x y z : R3) (hr : r ≠ 0) (hRho : ContDiffAt ℝ ∞ rho (x,y))
    (hE : HasFDerivAt E (r • J) z) (hx : x = E z) (hJ : J.IsInvertible)
    (hidentity : ∀ᶠ w in 𝓝 z, rho (E w,y) = (⟪w,w⟫_ℝ-1)/2) :
    ∀ X : R3, ((fderiv ℝ rho (x,y)).comp (ContinuousLinearMap.inl ℝ R3 R3)) X =
      r⁻¹ * ⟪z,ContinuousLinearMap.inverse J X⟫_ℝ := by
  have hmodel : HasFDerivAt (fun w : R3 => (⟪w,w⟫_ℝ-1)/2) (innerSL ℝ z) z := by
    have hh := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.sub_const 1).const_smul ((2 : ℝ)⁻¹)
    have hfactor : (2 : ℝ)⁻¹ • (2 • innerSL ℝ z) = innerSL ℝ z := by
      rw [two_smul,smul_add,← add_smul]
      norm_num
    have hfunc : (fun w : R3 => (⟪w,w⟫_ℝ-1)/2) =
        (2 : ℝ)⁻¹ • (fun w : R3 => ‖w‖^2-1) := by
      funext w
      simp only [Pi.smul_apply,smul_eq_mul,real_inner_self_eq_norm_sq,div_eq_mul_inv]
      ring
    rw [hfunc]
    simpa only [hfactor] using hh
  have hRho' : HasFDerivAt rho (fderiv ℝ rho (x,y)) (E z,y) := by
    rw [← hx]
    exact (hRho.differentiableAt (by simp)).hasFDerivAt
  have hpair := hE.prodMk (hasFDerivAt_const y z)
  have hcompose := hRho'.comp z hpair
  have hjet := hcompose.unique (hmodel.congr_of_eventuallyEq hidentity)
  intro X
  have hJI : J (ContinuousLinearMap.inverse J X) = X := by
    have hh := congrArg (fun A : R3 →L[ℝ] R3 => A X) hJ.self_comp_inverse
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using hh
  have hv := congrArg (fun A : R3 →L[ℝ] ℝ => A (ContinuousLinearMap.inverse J X)) hjet
  change fderiv ℝ rho (x,y) (r • J (ContinuousLinearMap.inverse J X),0) =
    ⟪z,ContinuousLinearMap.inverse J X⟫_ℝ at hv
  rw [hJI] at hv
  have hscale : (r • X,(0 : R3)) = r • (X,(0 : R3)) := by simp
  rw [hscale,map_smul,smul_eq_mul] at hv
  change fderiv ℝ rho (x,y) (X,0) = _
  calc
    fderiv ℝ rho (x,y) (X,0) = r⁻¹ * (r*fderiv ℝ rho (x,y) (X,0)) := by
      rw [← mul_assoc,inv_mul_cancel₀ hr,one_mul]
    _ = _ := by rw [hv]

/-- The exact covector formula is realized by the actual open reference-radius packet phase. -/
theorem exists_packet_referenceRadius_first_covector
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hR : 0 < Rstar)
    (y : R3) (hy : y ∈ P.centers)
    (hr : referenceRadius delta Rstar p L y ≤ 4*P.rho) (z : R3) (hz : ‖z‖ = 1) :
    let r0 := referenceRadius delta Rstar p L y
    let J := referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r0),z))
    let x := packetEndpoint S L P lam y r0 z
    ∃ U : Set (R3 × R3), ∃ rho : R3 × R3 → ℝ,
      IsOpen U ∧ (x,y) ∈ U ∧ ContDiffOn ℝ ∞ rho U ∧ rho (x,y) = 0 ∧
      (fderiv ℝ rho (x,y)).comp (ContinuousLinearMap.inl ℝ R3 R3) ≠ 0 ∧
      (∀ X : R3, ((fderiv ℝ rho (x,y)).comp (ContinuousLinearMap.inl ℝ R3 R3)) X =
        r0⁻¹ * ⟪z,ContinuousLinearMap.inverse J X⟫_ℝ) ∧
      ∀ᶠ b : R3 × R3 in 𝓝 (y,z),
        rho (packetEndpoint S L P lam b.1 (referenceRadius delta Rstar p L b.1) b.2,b.1) =
          (⟪b.2,b.2⟫_ℝ-1)/2 := by
  intro r0 J x
  obtain ⟨U,rho,hU,hxy,hsmooth,hzero,hne,hfixed,hfamily⟩ :=
    exists_packet_referenceRadius_open_first_phase S L P lam hlam delta Rstar p hd hR y hy hr z hz
  have hrpos : 0 < r0 := referenceRadius_pos delta Rstar p L y hd hR
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  have hE : HasFDerivAt (packetEndpoint S L P lam y r0) (r0 • J) z :=
    hasFDerivAt_framedScaledEndpoint_slice (fun a => (P.Phi lam a 1).1)
      (fun u => conformalReferenceGramFrameOperatorJoint S.g1 L (lam,u))
      (hTheta.comp (contDiff_const.prodMk contDiff_id)) y z r0
  have hz2 : z ∈ closedBall (0 : R3) 2 := by simp only [mem_closedBall,dist_zero_right,hz];norm_num
  have hrabs : |r0| ≤ 4*P.rho := by rw [abs_of_pos hrpos];exact hr
  have hInv : J.IsInvertible := packet_normalizedJacobian_isInvertible S L P lam hlam y hy r0 hrabs z hz2
  refine ⟨U,rho,hU,hxy,hsmooth,hzero,hne,?_,hfamily⟩
  exact first_partial_formula_of_normalized_sphere_identity rho (packetEndpoint S L P lam y r0) r0 J
    x y z hrpos.ne' (hsmooth.contDiffAt (hU.mem_nhds hxy)) hE rfl hInv hfixed

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
