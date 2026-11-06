import Calderon.ActualReferenceFinitePhysicalResidual
import Calderon.ActualFullPhysicalOperatorLinearity
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic ConnectionError
  ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint ActualFiniteHarmonicCore
  ActualFiniteHarmonicModel
attribute [local irreducible] referencePhysicalDensityOperator sphereSobolevInclusionL harmonicSphereSubspace
  nativePacketPhysicalDensityOperator referenceFinitePhysicalModelResidual
  referenceRadialEndpointInvertibleLocus referenceFramedNormalizedJacobian

def nativePacketFinitePhysicalModelResidual
    (hcalc:FixedSobolevCalculus) (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L:ℝ) (cover:NativeNormalCover S L)
    (q delta Rstar:ℝ) (p:ℕ) (A:smoothCompactFiniteSphereCore hO hD) (i:Fin cover.count) (y:R3):
    SphereSobolev (-(1/2:ℝ)):=
  let P:=cover.packet i
  referenceFinitePhysicalModelResidual S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
    hcalc hF hO hD tau0 S.g1_admissible S.g2 q delta Rstar p A y

theorem nativePacketPhysicalDensityOperator_finiteCore_eq_model_add_explicit_residual
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L q delta Rstar:ℝ) (p:ℕ)
    (cover:NativeNormalCover S L)
    (hCenter:∀ j:Fin cover.count,∀ z∈(cover.packet j).centers,‖z-(cover.packet j).y0‖ < (cover.packet j).rho)
    (hd:0 < delta) (hRs:0 < Rstar) (hLam:q∈Icc (0:ℝ) cover.dilationCeiling)
    (i:Fin cover.count) (y:R3) (hy:y∈(cover.packet i).centers)
    (hrceil:referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (A:smoothCompactFiniteSphereCore hO hD):
    nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
      (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y=
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevZeroEquiv hO hD
          ((nativeNormalizedSecondReferenceModel hO hD hF S.g1 S.g2 S.g1_admissible L q delta Rstar p
            S.g2_admissible hd hRs A:R3→SphereL2) y))+
        nativePacketFinitePhysicalModelResidual hcalc hF hO hD tau0 S L cover q delta Rstar p A i y := by
  let P:=cover.packet i
  let R:R3→ℝ:=referenceRadius delta Rstar p L
  have hq:q∈Icc (0:ℝ) 1:=⟨hLam.1,hLam.2.trans cover.dilation_le_one⟩
  have hc:‖y-P.y0‖ < 4*P.rho:=(P.centers_room y hy).1
  have hSmall:‖y-P.y0‖ ≤ P.rho:=(hCenter i y hy).le
  have hPos:0 < R y:=referenceRadius_pos delta Rstar p L y hd hRs
  have hAbs:|R y| < 4*P.rho:=by
    rw [abs_of_pos hPos]
    exact hrceil.trans (cover.radius_room i)
  have hInv (x:UnitSphere):(referenceFramedNormalizedJacobian S.g1 L P.Phi (q,((y,R y),x.val))).IsInvertible:=by
    apply isInvertible_of_operatorMatrixMap_det_ne_zero
    exact referenceFramedNormalizedJacobian_det_ne_zero_on_closedDoubleBall S.g1 S.g1_admissible L P.y0 P.Phi
      P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data q hq y hc.le (R y) hAbs.le x.val
      (closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall x.property))
  have hp:=referenceRadialEndpointInvertibleLocus_mem_on_actual_room S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo
    P.Cgeo P.rho P.H P.a P.w P.native_data hcalc hreg hF hO hD tau0 q hq y hc.le (R y) hAbs.le
  have h:=referencePhysicalDensityOperator_finiteCore_eq_nativeModel_add_explicit_residual
    S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data hcalc hF hO hD tau0
      S.g1_admissible S.g2 S.g2_admissible hreg q hq delta Rstar p hd hRs A y hSmall hInv hp
  have hJ (v:SphereL2) :
      ((sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
        (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap) v =
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD v) := by rfl
  dsimp only at h
  rw [hJ] at h
  simpa only [nativePacketPhysicalDensityOperator,nativePacketFinitePhysicalModelResidual,P,R] using h

theorem exists_actual_full_model_error_field_with_explicit_residual_graph
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L q delta Rstar:ℝ) (p:ℕ)
    (cover:NativeNormalCover S L)
    (hCenter:∀ j:Fin cover.count,∀ z∈(cover.packet j).centers,‖z-(cover.packet j).y0‖ < (cover.packet j).rho)
    (hd:0 < delta) (hRs:0 < Rstar) (hLam:q∈Icc (0:ℝ) cover.dilationCeiling)
    (hRadius:∀ y∈cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (K:Set R3) (F:smoothCompactFiniteSphereCore hO hD→R3→SphereL2)
    (hFData:∀ A:smoothCompactFiniteSphereCore hO hD,tsupport (A:R3→SphereL2)⊆K →
      ContDiff ℝ ∞ (F A) ∧ HasCompactSupport (F A) ∧ tsupport (F A)⊆tsupport (A:R3→SphereL2) ∧
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (F A y))=
        nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
          (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y)
    (A:smoothCompactFiniteSphereCore hO hD) (hA:tsupport (A:R3→SphereL2)⊆K):
    ∃ E:R3→SphereL2,ContDiff ℝ ∞ E ∧ HasCompactSupport E ∧
      (∀ y:R3,F A y=
        ((nativeNormalizedSecondReferenceModel hO hD hF S.g1 S.g2 S.g1_admissible L q delta Rstar p
          S.g2_admissible hd hRs A:R3→SphereL2) y)+E y) ∧
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (E y))=
        nativePacketFinitePhysicalModelResidual hcalc hF hO hD tau0 S L cover q delta Rstar p A i y := by
  let M:smoothCompactFiniteSphereCore hO hD:=
    nativeNormalizedSecondReferenceModel hO hD hF S.g1 S.g2 S.g1_admissible L q delta Rstar p
      S.g2_admissible hd hRs A
  let E:R3→SphereL2:=fun y=>F A y-(M:R3→SphereL2) y
  have hOut:=hFData A hA
  have hE:ContDiff ℝ ∞ E:=hOut.1.sub M.property.1
  have hEc:HasCompactSupport E:=hOut.2.1.sub M.property.2.1
  refine ⟨E,hE,hEc,?_,?_⟩
  · intro y
    change F A y=(M:R3→SphereL2) y+(F A y-(M:R3→SphereL2) y)
    abel
  · intro i y hy
    let J:SphereL2→L[ℝ]SphereSobolev (-(1/2:ℝ)):=
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
        (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
    have hP:=nativePacketPhysicalDensityOperator_finiteCore_eq_model_add_explicit_residual
      hcalc hreg hF hO hD tau0 S L q delta Rstar p cover hCenter hd hRs hLam i y hy.2
      (hRadius y (interior_subset hy.1)) A
    have hGraph:J (F A y)=J ((M:R3→SphereL2) y)+
        nativePacketFinitePhysicalModelResidual hcalc hF hO hD tau0 S L cover q delta Rstar p A i y:=
      (hOut.2.2.2 i y hy).trans hP
    change J (F A y-(M:R3→SphereL2) y)=_
    exact (map_sub J _ _).trans ((congrArg (fun v=>v-J ((M:R3→SphereL2) y)) hGraph).trans
      (by abel))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
