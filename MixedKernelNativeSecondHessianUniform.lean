import MixedKernelNativeYYErrorAlgebra
import MixedKernelNativeReferenceAngularBounds
import MixedKernelNativeJacobiFirstBounds
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth MetricOperator NormalCoordinatesFrame
open scoped ContDiff InnerProductSpace Topology

/-- The ACTUAL reference yy Hessian columns have one uniform quadratic error bound. -/
theorem exists_packet_second_hessian_column_error_bound
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam ∈ Icc (0 : ℝ) 1,
      ∀ y : R3, y ∈ P.centers → ∀ r : ℝ, 0 < r → r ≤ min 1 (4*P.rho) →
      ∀ z : R3, ‖z‖=1 →
        let x := packetEndpoint S L P lam y r z
        let F : R3 → R3 →L[ℝ] R3 := fun Y => conformalReferenceGramFrameOperatorJoint S.g1 L (lam,Y)
        let Gamma := coordinateConnectionField
          (inverseMetricField (metricOperatorField (conformalReferenceMatrix S.g1 L lam)))
          (metricOperatorField (conformalReferenceMatrix S.g1 L lam))
        ∃ U0 : Set (R3 × R3), ∃ rho : R3 × R3 → ℝ,
          IsOpen U0 ∧ (x,y) ∈ U0 ∧ ContDiffOn ℝ ∞ rho U0 ∧ rho (x,y)=0 ∧
          (∀ᶠ b : R3 × R3 in 𝓝 (y,z),
            rho (packetEndpoint S L P lam b.1 r b.2,b.1) = (⟪b.2,b.2⟫_ℝ-1)/2) ∧
          ∀ i j : Fin 3,
            |r^2*(fderiv ℝ (fderiv ℝ rho) (x,y) (0,F y (coordinateVector i)) (0,F y (coordinateVector j))-
              fderiv ℝ rho (x,y) (0,Gamma y (F y (coordinateVector i)) (F y (coordinateVector j))))-
              ⟪coordinateVector i,coordinateVector j⟫_ℝ| ≤ C*r^2 := by
  obtain ⟨K0,hK0,HK0⟩ := exists_packet_reference_frame_connection_angular_bounds S L P
  obtain ⟨D,hD,HD⟩ := exists_packet_jacobi_first_bounds S L P
  obtain ⟨Dv,hDv,HDv⟩ := exists_packet_jacobi_synthesis_bound S L P
  let K : ℝ := K0+D+Dv+1
  have hK : 1 ≤ K := by dsimp [K];linarith
  have hK0K : K0 ≤ K := by dsimp [K];linarith
  have hDK : D ≤ K := by dsimp [K];linarith
  have hDvK : Dv ≤ K := by dsimp [K];linarith
  refine ⟨3*K+6*K^2+1,by nlinarith [sq_nonneg K],?_⟩
  intro lam hlam y hy r hrpos hr z hz x F Gamma
  have hr1 : r ≤ 1 := hr.trans (min_le_left _ _)
  have hrrho : r ≤ 4*P.rho := hr.trans (min_le_right _ _)
  have hyClosed : ‖y-P.y0‖ ≤ 4*P.rho := (P.centers_room y hy).1.le
  have hrAbs : |r| ≤ 4*P.rho := by simpa only [abs_of_pos hrpos] using hrrho
  have hzClosed : z ∈ closedBall (0 : R3) 2 := by simp only [mem_closedBall,dist_zero_right,hz];norm_num
  have hFrames := HK0 lam hlam y hyClosed
  have hBasis (i : Fin 3) : ‖coordinateVector i‖=1 := by simp [coordinateVector]
  obtain ⟨U0,rho,hU0,hxy,hRho,hzero,hfamily,Hformula⟩ :=
    exists_packet_constant_radius_second_hessian_formula S L P lam hlam r hrpos y hy hrrho z hz
  refine ⟨U0,rho,hU0,hxy,hRho,hzero,hfamily,?_⟩
  intro i j
  let VR : (R3 × R3) → R3 →L[ℝ] R3 := fun b => frameOperator
    (fun k => referenceFramedJacobiVelocityRemainder S.g1 L P.Phi k (lam,((b.1,r),b.2)))
  let X := F y (coordinateVector i)
  let Omega := framedParallelAngularOperator F Gamma y X
  let Zp := Omega z-r⁻¹ • coordinateVector i-r • VR (y,z) (coordinateVector i)
  let Vj : R3 × R3 → R3 := fun b => VR b (coordinateVector j)
  have hO : ‖Omega‖ ≤ K := (hFrames.2.2 i).trans hK0K
  have hX : ‖X‖ ≤ K := by
    have hh := (F y).le_opNorm (coordinateVector i)
    rw [hBasis i,mul_one] at hh
    exact hh.trans (hFrames.1.trans hK0K)
  have hVR : ‖VR (y,z)‖ ≤ K := (HDv lam hlam y hyClosed r hrAbs z hzClosed).trans hDvK
  have hVi : ‖VR (y,z) (coordinateVector i)‖ ≤ K := by
    simpa only [VR,frameOperator_coordinateVector] using (HD lam hlam y hyClosed r hrAbs z hzClosed i).1.trans hDK
  have hVj : ‖Vj (y,z)‖ ≤ K := by
    simpa only [Vj,VR,frameOperator_coordinateVector] using (HD lam hlam y hyClosed r hrAbs z hzClosed j).1.trans hDK
  have hDVj : ‖fderiv ℝ Vj (y,z)‖ ≤ K := by
    simpa only [Vj,VR,frameOperator_coordinateVector] using (HD lam hlam y hyClosed r hrAbs z hzClosed j).2.trans hDK
  have hSkew : ⟪Omega z,coordinateVector j⟫_ℝ = -⟪z,Omega (coordinateVector j)⟫_ℝ := by
    simpa only [Omega,framedParallelAngularOperator_apply,F,Gamma] using
      native_parallelAngularVelocity_skew S.g1 S.g1_admissible L lam y X z (coordinateVector j)
  have hBound := second_hessian_column_error_of_formula Omega (VR (y,z)) (fderiv ℝ Vj (y,z)) r K
    (fderiv ℝ (fderiv ℝ rho) (x,y) (0,X) (0,F y (coordinateVector j))-
      fderiv ℝ rho (x,y) (0,Gamma y X (F y (coordinateVector j))))
    z (coordinateVector i) (coordinateVector j) X (VR (y,z) (coordinateVector i)) (Vj (y,z)) Zp
    hrpos hr1 hK hz (hBasis i) (hBasis j) hO hVR hDVj hX hVi hVj rfl hSkew (Hformula i j)
  exact hBound.trans (by nlinarith only [sq_nonneg r])

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
