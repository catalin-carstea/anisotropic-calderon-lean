import Calderon.MixedKernelConstruction.MixedKernelNativePacketInverse
import Calderon.ActualFramedJacobiVelocityRemainder
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError MetricOperator
open scoped ContDiff InnerProductSpace Topology

/-- The literal positive pullback identity gives invertibility on the whole CLOSED original room. -/
theorem packet_closedRoom_normalizedJacobian_isInvertible (S : KnownSideSourceData) (L : ℝ)
    (P : NativeNormalPacket S L) (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (y : R3) (hy : ‖y-P.y0‖ ≤ 4*P.rho) (r : ℝ) (hr : |r| ≤ 4*P.rho)
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    (referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),z))).IsInvertible := by
  let J := referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),z))
  let M := matrixOperatorMap (P.H ((lam,(y,r)),z))
  have hPB := referenceFramedOriginalNormalizedMetric_eq S.g1 S.g1_admissible L P.y0
    P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
    lam hlam y hy r hr z hz
  have hPos : (P.H ((lam,(y,r)),z)).PosDef := by
    rcases P.native_data.1 with ⟨_,_,_,_,_,_,_,hPos,_,_,_,_,_,_,_⟩
    exact hPos _
  have hunit : IsUnit M := hPos.isUnit.map matrixOperatorAlgEquiv.toMonoidHom
  have hker (v : R3) (hv : J v = 0) : v = 0 := by
    have hzero := congrArg (fun A : R3 →L[ℝ] R3 => A v) hPB
    change J.adjoint (metricOperatorField S.g1
      (lam • referenceFramedPhysicalEndpoint S.g1 L P.Phi (lam,((y,r),z))) (J v)) =
      Real.exp (2*L*referenceRescaledDepth S.g1 L P.Phi (lam,(y,r)) z) • M v at hzero
    rw [hv,map_zero,map_zero] at hzero
    have hMv : M v = 0 := (smul_eq_zero.mp hzero.symm).resolve_left (Real.exp_ne_zero _)
    have hi := congrArg (fun A : R3 →L[ℝ] R3 => A v) (Ring.inverse_mul_cancel M hunit)
    change Ring.inverse M (M v) = v at hi
    rw [hMv,map_zero] at hi
    exact hi.symm
  apply isInvertible_compactChart_endomorphism
  intro v w hvw
  exact sub_eq_zero.mp (hker (v-w) (by rw [map_sub,hvw,sub_self]))

/-- Finite joint derivatives of the ACTUAL Jacobi remainder are bounded on one fixed compact packet room. -/
theorem exists_packet_closedRoom_jacobi_bounds
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L) :
    ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ N →
      ∀ a ∈ conformalReferenceFramedMetricRoom P.y0 (4*P.rho), ∀ i : Fin 3,
        ‖iteratedFDeriv ℝ j (referenceFramedJacobiVelocityRemainder S.g1 L P.Phi i) a‖ ≤ D := by
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) :=
    hEnd.2.2.2.2.2.2.2.1
  apply exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
    (referenceFramedJacobiVelocityRemainder S.g1 L P.Phi)
    (conformalReferenceFramedMetricRoom P.y0 (4*P.rho))
    (isCompact_Icc.prod (((isCompact_closedBall _ _).prod isCompact_Icc).prod
      (isCompact_closedBall _ _)))
  intro i a ha
  have hy : ‖a.2.1.1-P.y0‖ ≤ 4*P.rho := by
    simpa only [mem_closedBall,dist_eq_norm] using ha.2.1.1
  exact contDiffAt_referenceFramedJacobiVelocityRemainder S.g1 S.g1_admissible L P.Phi hTheta
    i a (packet_closedRoom_normalizedJacobian_isInvertible S L P a.1 ha.1 a.2.1.1 hy
      a.2.1.2 (abs_le.mpr ha.2.1.2) a.2.2 ha.2.2)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
