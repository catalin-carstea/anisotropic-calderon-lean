import Calderon.ActualUniformFullCutoffCommutator
import Calderon.ActualNativeCoverConstantForcing
import Calderon.ActualEligibleDensityCutoffPDE
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
open ConnectionError ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint MetricOperator MetricVolume ActualFiniteHarmonicCore
attribute [local irreducible] referencePhysicalDensityOperator sphereSobolevInclusionL
  referenceDensityScalarCutoffCommutator referenceRadialEndpointInvertibleLocus referenceFramedNormalizedJacobian

def nativeNormalizedCutoffPhysicalOperator
    (hcalc:FixedSobolevCalculus) (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics)
    (hD:DenseSphereHarmonics) (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L:ℝ)
    (cover:NativeNormalCover S L) (chi:R3→ℝ) (lambda delta Rstar:ℝ) (p:ℕ)
    (Psi:R3→SphereSobolev (3/2:ℝ)) (i:Fin cover.count) (y:R3):SphereSobolev (-(1/2:ℝ)) :=
  let P:=cover.packet i
  referencePhysicalDensityOperator S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho
    P.H P.a P.w P.native_data S.g1_admissible hcalc hF hO hD tau0 S.g2 lambda
    (referenceRadius delta Rstar p L) (fun z => chi z • (Psi z-sphereSobolevConstantOne (3/2:ℝ))) y

theorem native_cutoff_rhs_half_lift_of_eligible_density
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L lambda delta Rstar bound separation:ℝ) (p:ℕ)
    (cover:NativeNormalCover S L) (K:ConstructedMixedKernel S L lambda delta Rstar bound separation p cover)
    (hlam:0 < lambda) (hlamRoom:lambda ≤ cover.dilationCeiling) (hd:0 < delta) (hRs:0 < Rstar)
    (hRadius:∀ y∈cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (Psi:R3→SphereSobolev (3/2:ℝ)) (hPsi:ContDiff ℝ ∞ Psi) (hPsic:HasCompactSupport Psi)
    (hRep:RepresentsNativeMixedKernelDensity hO hD tau0 S L lambda delta Rstar bound separation p cover K Psi)
    (chi:R3→ℝ) (hchi:ContDiff ℝ ∞ chi) (i:Fin cover.count) (y:R3)
    (hy:y∈interior cylinder∩(cover.packet i).centers) (hchiOne:|chi y| ≤ 1)
    (Dconst Dcomm:ℝ) (vConst:SphereSobolev (1/2:ℝ)) (hv:‖vConst‖ ≤ Dconst)
    (hvEq:sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) vConst=
      referencePhysicalDensityOperator S.g1 L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B
        (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho (cover.packet i).H (cover.packet i).a
        (cover.packet i).w (cover.packet i).native_data S.g1_admissible hcalc hF hO hD tau0 S.g2 lambda
        (referenceRadius delta Rstar p L) (fun _ => sphereSobolevConstantOne (3/2:ℝ)) y)
    (hComm:‖nativeDensityCutoffCommutator hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p Psi i y‖ ≤ Dcomm):
    ∃ v:SphereSobolev (1/2:ℝ),‖v‖ ≤ Dconst+Dcomm ∧
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) v=
      nativeNormalizedCutoffPhysicalOperator hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p Psi i y := by
  let P:=cover.packet i
  let R:R3→ℝ := referenceRadius delta Rstar p L
  have hR:ContDiff ℝ ∞ R := contDiff_referenceRadius_actual delta Rstar p L hd hRs
  have hq:lambda∈Icc (0:ℝ) 1 := ⟨hlam.le,hlamRoom.trans cover.dilation_le_one⟩
  have hPos:0 < R y := referenceRadius_pos delta Rstar p L y hd hRs
  have hCenter:‖y-P.y0‖ ≤ 4*P.rho := (P.centers_room y hy.2).1.le
  have hAbs:|R y| ≤ 4*P.rho := by rw [abs_of_pos hPos];exact ((hRadius y (interior_subset hy.1)).trans (cover.radius_room i)).le
  have hInv (x:UnitSphere):(referenceFramedNormalizedJacobian S.g1 L P.Phi (lambda,((y,R y),x.val))).IsInvertible := by
    apply isInvertible_of_operatorMatrixMap_det_ne_zero
    exact referenceFramedNormalizedJacobian_det_ne_zero_on_closedDoubleBall S.g1 S.g1_admissible L P.y0 P.Phi P.B
      P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data lambda hq y hCenter (R y) hAbs x.val
      (closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall x.property))
  have hp:=referenceRadialEndpointInvertibleLocus_mem_on_actual_room S.g1 S.g1_admissible L P.y0 P.Phi P.B
    P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data hcalc hreg hF hO hD tau0 lambda hq y hCenter (R y) hAbs
  have hEquation:=referencePhysicalDensityOperator_eq_zero_of_eligible_native_density
    hcalc hreg hF hO hD tau0 hKernel S L lambda delta Rstar bound separation p cover K hd hRs hlam hlamRoom
    hRadius Psi hPsi hPsic hRep i y hy
  have hRhs:=referencePhysicalDensityOperator_cutoff_sub_of_eq_zero S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho
    P.H P.a P.w P.native_data S.g1_admissible hcalc hF hO hD tau0 S.g2 hreg lambda R chi Psi
    (fun _ => sphereSobolevConstantOne (3/2:ℝ)) hPsi contDiff_const hchi y hR.contDiffAt hPos.ne' hInv hp hEquation
  let comm:=nativeDensityCutoffCommutator hcalc hF hO hD tau0 S L cover chi lambda delta Rstar p Psi i y
  refine ⟨-(chi y • vConst)+comm,?_,?_⟩
  · have hsm:‖chi y • vConst‖ ≤ Dconst := by
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hchiOne (norm_nonneg _)).trans (by simpa only [one_mul] using hv)
    exact (norm_add_le _ _).trans (by rw [norm_neg];linarith only [hsm,hComm])
  · rw [map_add,map_neg,map_smul,hvEq]
    dsimp only [nativeNormalizedCutoffPhysicalOperator]
    exact hRhs.symm

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
