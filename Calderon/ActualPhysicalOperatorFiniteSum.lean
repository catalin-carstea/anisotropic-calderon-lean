import Calderon.ActualPhysicalDensityOperatorSubtraction
import Calderon.ActualPacketPhysicalOperatorCoherence
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection ActualNormalizedSecondMetricDrift
variable (g:MatrixField) (L:ℝ) (y0:R3)
  (Phi:ℝ→(R3×R3)→ℝ→R3×R3) (B:Set (R3×R3)) (eps C rho:ℝ)
  (H a:(ℝ×(R3×ℝ))×R3→Matrix (Fin 3) (Fin 3) ℝ)
  (w:(ℝ×(R3×ℝ))×R3→ℝ)
  (hData:JointConformalReferenceFramedDriftData g L y0 Phi B eps C rho H a w)
  (hg:IsAdmissibleMetric g) (hcalc:FixedSobolevCalculus)
  (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics) (tau0:UnitBallValueTrace)
attribute [local irreducible] referencePhysicalDensityOperator referenceHighDensityFirstAction referenceLowerDensityFirstAction
  sphereSobolevInclusionL referenceRadialEndpointInvertibleLocus referenceFramedNormalizedJacobian harmonicSphereSubspace

variable (g2:MatrixField) (hreg:FixedDirichletRegularity) (q:ℝ) (R:R3→ℝ) (y:R3)
  (hR:ContDiffAt ℝ ∞ R y) (hr:R y≠0)
  (hInv:∀ x:UnitSphere,(referenceFramedNormalizedJacobian g L Phi (q,((y,R y),x.val))).IsInvertible)
  (hp:(q,(y,R y))∈referenceRadialEndpointInvertibleLocus g L y0 Phi B eps C rho H a w hData hcalc hF hO hD tau0)

include hreg hR hr hInv hp

theorem referencePhysicalDensityOperator_zero_of_actual_room:
    referencePhysicalDensityOperator g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 g2 q R
      (fun _:R3 => (0:SphereSobolev (3/2:ℝ))) y=0 := by
  have h:=referencePhysicalDensityOperator_sub g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0
    g2 hreg q R (fun _:R3 => (0:SphereSobolev (3/2:ℝ))) (fun _:R3 => (0:SphereSobolev (3/2:ℝ)))
    contDiff_const contDiff_const y hR hr hInv hp
  simpa only [sub_self] using h

theorem referencePhysicalDensityOperator_add_of_actual_room
    (u v:R3→SphereSobolev (3/2:ℝ)) (hu:ContDiff ℝ ∞ u) (hv:ContDiff ℝ ∞ v):
    referencePhysicalDensityOperator g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 g2 q R
      (fun x => u x+v x) y=
    referencePhysicalDensityOperator g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 g2 q R u y+
      referencePhysicalDensityOperator g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 g2 q R v y := by
  have hZero:=referencePhysicalDensityOperator_zero_of_actual_room g L y0 Phi B eps C rho H a w hData hg
    hcalc hF hO hD tau0 g2 hreg q R y hR hr hInv hp
  have hNeg:=referencePhysicalDensityOperator_sub g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0
    g2 hreg q R (fun _:R3 => (0:SphereSobolev (3/2:ℝ))) v contDiff_const hv y hR hr hInv hp
  rw [hZero] at hNeg
  have hNeg':referencePhysicalDensityOperator g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 g2 q R
      (fun x => -v x) y= -referencePhysicalDensityOperator g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 g2 q R v y := by
    simpa only [zero_sub] using hNeg
  have h:=referencePhysicalDensityOperator_sub g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0
    g2 hreg q R u (fun x => -v x) hu hv.neg y hR hr hInv hp
  rw [hNeg'] at h
  simpa only [sub_neg_eq_add] using h

theorem referencePhysicalDensityOperator_finset_sum_of_actual_room
    {ι:Type*} (s:Finset ι) (u:ι→R3→SphereSobolev (3/2:ℝ)) (hu:∀ i,ContDiff ℝ ∞ (u i)):
    referencePhysicalDensityOperator g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 g2 q R
      (fun x => ∑ i∈s,u i x) y=
      ∑ i∈s,referencePhysicalDensityOperator g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 g2 q R (u i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using referencePhysicalDensityOperator_zero_of_actual_room
        g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 g2 hreg q R y hR hr hInv hp
  | @insert i s hi ih =>
      have hSum:ContDiff ℝ ∞ (fun x => ∑ j∈s,u j x) := ContDiff.sum (fun j _ => hu j)
      have h:=referencePhysicalDensityOperator_add_of_actual_room g L y0 Phi B eps C rho H a w hData hg
        hcalc hF hO hD tau0 g2 hreg q R y hR hr hInv hp (u i) (fun x => ∑ j∈s,u j x) (hu i) hSum
      simpa only [Finset.sum_insert hi,ih] using h

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic ConnectionError
  ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint
attribute [local irreducible] referencePhysicalDensityOperator sphereSobolevInclusionL harmonicSphereSubspace
  referenceRadialEndpointInvertibleLocus referenceFramedNormalizedJacobian

theorem nativePacketPhysicalDensityOperator_sum
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L lambda delta Rstar:ℝ) (p:ℕ)
    (cover:NativeNormalCover S L) (hd:0 < delta) (hRs:0 < Rstar)
    (hLam:lambda∈Icc (0:ℝ) cover.dilationCeiling) (i:Fin cover.count) (y:R3)
    (hy:y∈(cover.packet i).centers) (hrceil:referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (n:ℕ) (u:Fin n→R3→SphereSobolev (3/2:ℝ)) (hu:∀ j,ContDiff ℝ ∞ (u j)):
    nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p
      (fun x => ∑ j,u j x) i y=
      ∑ j,nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p (u j) i y := by
  let P:=cover.packet i
  let R:R3→ℝ := referenceRadius delta Rstar p L
  have hq:lambda∈Icc (0:ℝ) 1 := ⟨hLam.1,hLam.2.trans cover.dilation_le_one⟩
  have hc:‖y-P.y0‖ < 4*P.rho := (P.centers_room y hy).1
  have hPos:0 < R y := referenceRadius_pos delta Rstar p L y hd hRs
  have hAbs:|R y| < 4*P.rho := by rw [abs_of_pos hPos];exact hrceil.trans (cover.radius_room i)
  have hR:ContDiff ℝ ∞ R := contDiff_referenceRadius_actual delta Rstar p L hd hRs
  have hInv (x:UnitSphere):(referenceFramedNormalizedJacobian S.g1 L P.Phi (lambda,((y,R y),x.val))).IsInvertible := by
    apply isInvertible_of_operatorMatrixMap_det_ne_zero
    exact referenceFramedNormalizedJacobian_det_ne_zero_on_closedDoubleBall S.g1 S.g1_admissible L P.y0 P.Phi
      P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data lambda hq y hc.le (R y) hAbs.le x.val
      (closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall x.property))
  have hp:=referenceRadialEndpointInvertibleLocus_mem_on_actual_room S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo
    P.Cgeo P.rho P.H P.a P.w P.native_data hcalc hreg hF hO hD tau0 lambda hq y hc.le (R y) hAbs.le
  have h:=referencePhysicalDensityOperator_finset_sum_of_actual_room S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho
    P.H P.a P.w P.native_data S.g1_admissible hcalc hF hO hD tau0 S.g2 hreg lambda R y hR.contDiffAt hPos.ne' hInv hp
    Finset.univ u hu
  simpa only [nativePacketPhysicalDensityOperator] using h

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
