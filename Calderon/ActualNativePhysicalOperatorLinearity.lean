import Calderon.ActualFiniteCoreSobolevLiftLinearity
import Calderon.ActualDensityScalarCutoff
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic ConnectionError
  ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint
attribute [local irreducible] referencePhysicalDensityOperator sphereSobolevInclusionL harmonicSphereSubspace
  referenceRadialEndpointInvertibleLocus referenceFramedNormalizedJacobian

theorem nativePacketPhysicalDensityOperator_smul
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L lambda delta Rstar:ℝ) (p:ℕ)
    (cover:NativeNormalCover S L) (hd:0 < delta) (hRs:0 < Rstar)
    (hLam:lambda∈Icc (0:ℝ) cover.dilationCeiling) (i:Fin cover.count) (y:R3)
    (hy:y∈(cover.packet i).centers) (hrceil:referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (a:ℝ) (u:R3→SphereSobolev (3/2:ℝ)) (hu:ContDiff ℝ ∞ u):
    nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p
      (fun x=>a • u x) i y=
      a • nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p u i y := by
  let P:=cover.packet i
  let R:R3→ℝ:=referenceRadius delta Rstar p L
  have hq:lambda∈Icc (0:ℝ) 1:=⟨hLam.1,hLam.2.trans cover.dilation_le_one⟩
  have hc:‖y-P.y0‖ < 4*P.rho:=(P.centers_room y hy).1
  have hPos:0 < R y:=referenceRadius_pos delta Rstar p L y hd hRs
  have hAbs:|R y| < 4*P.rho:=by
    rw [abs_of_pos hPos]
    exact hrceil.trans (cover.radius_room i)
  have hR:ContDiff ℝ ∞ R:=contDiff_referenceRadius_actual delta Rstar p L hd hRs
  have hInv (x:UnitSphere):(referenceFramedNormalizedJacobian S.g1 L P.Phi (lambda,((y,R y),x.val))).IsInvertible:=by
    apply isInvertible_of_operatorMatrixMap_det_ne_zero
    exact referenceFramedNormalizedJacobian_det_ne_zero_on_closedDoubleBall S.g1 S.g1_admissible L P.y0 P.Phi
      P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data lambda hq y hc.le (R y) hAbs.le x.val
      (closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall x.property))
  have hp:=referenceRadialEndpointInvertibleLocus_mem_on_actual_room S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo
    P.Cgeo P.rho P.H P.a P.w P.native_data hcalc hreg hF hO hD tau0 lambda hq y hc.le (R y) hAbs.le
  have h:=referencePhysicalDensityOperator_smul_sub S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho
    P.H P.a P.w P.native_data S.g1_admissible hcalc hF hO hD tau0 S.g2 hreg lambda R
      (fun _=>a) u y hu contDiff_const hR.contDiffAt hPos.ne' hInv hp
  have hComm:referenceDensityScalarCutoffCommutator S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho
      P.H P.a P.w P.native_data S.g1_admissible hcalc hF hO hD tau0 S.g2 lambda R
      (fun _=>a) u y=0:=by
    simp [referenceDensityScalarCutoffCommutator,referenceFrameScalarDerivative,referenceFrameScalarHessian]
  rw [hComm,map_zero,sub_eq_zero] at h
  exact h

theorem nativePacketPhysicalDensityOperator_add
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L lambda delta Rstar:ℝ) (p:ℕ)
    (cover:NativeNormalCover S L) (hd:0 < delta) (hRs:0 < Rstar)
    (hLam:lambda∈Icc (0:ℝ) cover.dilationCeiling) (i:Fin cover.count) (y:R3)
    (hy:y∈(cover.packet i).centers) (hrceil:referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (u v:R3→SphereSobolev (3/2:ℝ)) (hu:ContDiff ℝ ∞ u) (hv:ContDiff ℝ ∞ v):
    nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p
      (fun x=>u x+v x) i y=
      nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p u i y+
      nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p v i y := by
  have h:=nativePacketPhysicalDensityOperator_sum hcalc hreg hF hO hD tau0 S L lambda delta Rstar p
    cover hd hRs hLam i y hy hrceil 2 (fun j=>![u,v] j) (by intro j;fin_cases j;exact hu;exact hv)
  simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using h

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
