import Calderon.ActualPacketPhysicalOperatorPairing
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic ConnectionError
  ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint MetricVolume MetricOperator
  NativeSmoothSharpTraceCompletion ActualNormalizedSecondMetricDrift
attribute [local irreducible] referencePhysicalDensityOperator sphereSobolevInclusionL
  sphereSobolevDualPairing nativeMixedKernelDensityFunctional nativePacketPhysicalDensityOperator harmonicSphereSubspace

theorem nativePacketPhysicalHalfTrace_eq_on_overlap
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L:ℝ) (cover:NativeNormalCover S L)
    (i j:Fin cover.count) (q:ℝ) (hq:q∈Icc (0:ℝ) cover.dilationCeiling)
    (y:R3) (hy:y∈(cover.packet i).centers∩(cover.packet j).centers)
    (r:ℝ) (hr:0 < r) (hrceil:r < cover.radiusCeiling) (u:SmoothData):
    smoothHalfTrace hF hO hD tau0 (referencePhysicalPullbackData S.g1 S.g1_admissible L
      (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).native_data.1.1.1 q y r u)=
    smoothHalfTrace hF hO hD tau0 (referencePhysicalPullbackData S.g1 S.g1_admissible L
      (cover.packet j).y0 (cover.packet j).Phi (cover.packet j).B (cover.packet j).native_data.1.1.1 q y r u) := by
  have hValue:smoothSphereValue (referencePhysicalPullbackData S.g1 S.g1_admissible L
      (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).native_data.1.1.1 q y r u)=
      smoothSphereValue (referencePhysicalPullbackData S.g1 S.g1_admissible L
      (cover.packet j).y0 (cover.packet j).Phi (cover.packet j).B (cover.packet j).native_data.1.1.1 q y r u) := by
    ext x
    change u.1 (packetEndpoint S L (cover.packet i) q y r x.val)=u.1 (packetEndpoint S L (cover.packet j) q y r x.val)
    rw [cover.endpoint_coherence i j q hq y hy r hr hrceil x.val
      (closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall x.property))]
  apply sphereSobolev_ext (1/2:ℝ)
  intro k
  rw [sphereSobolevCoefficientL_smoothHalfTrace,sphereSobolevCoefficientL_smoothHalfTrace,
    tau0.valueTrace_smooth,tau0.valueTrace_smooth,hValue]

theorem nativePacketPhysicalDensityOperator_eq_on_overlap
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L lambda delta Rstar:ℝ) (p:ℕ) (cover:NativeNormalCover S L)
    (hd:0 < delta) (hRs:0 < Rstar) (hLam:lambda∈Icc (0:ℝ) cover.dilationCeiling)
    (i j:Fin cover.count) (y:R3) (hy:y∈(cover.packet i).centers∩(cover.packet j).centers)
    (hrceil:referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (Psi:R3→SphereSobolev (3/2:ℝ)) (hPsi:ContDiff ℝ ∞ Psi):
    nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p Psi i y=
      nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p Psi j y := by
  let R:R3→ℝ := referenceRadius delta Rstar p L
  let r:=R y
  let op:Fin cover.count→SphereSobolev (-(1/2:ℝ)) := fun k =>
    nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p Psi k y
  have hR:ContDiff ℝ ∞ R := contDiff_referenceRadius_actual delta Rstar p L hd hRs
  have hrpos:0 < r := referenceRadius_pos delta Rstar p L y hd hRs
  change op i=op j
  apply sub_eq_zero.mp
  apply eq_zero_of_actualPacketPhysicalHarmonicHalfTrace_pairing_eq_zero
    hcalc hreg hF hO hD tau0 S L cover i lambda hLam y hy.1 r hrpos hrceil (op i-op j)
  intro z hz
  obtain ⟨u,V,hV,hCover,hPhys,hzEq⟩ := hz
  have hCoverJ:packetEndpoint S L (cover.packet j) lambda y r '' closedBall (0:R3) 1⊆V := by
    rintro t ⟨x,hx,rfl⟩
    apply hCover
    refine ⟨x,hx,?_⟩
    exact cover.endpoint_coherence i j lambda hLam y hy r hrpos hrceil x
      (closedBall_subset_closedBall (by norm_num) hx)
  have hPi:=nativePacketPhysicalDensityOperator_pairing_physical_harmonic_test hcalc hreg hF hO hD tau0 hKernel
    S L lambda delta Rstar p cover hd hRs hLam i y hy.1 hrceil Psi hPsi V hV u hCover hPhys
  have hPj:=nativePacketPhysicalDensityOperator_pairing_physical_harmonic_test hcalc hreg hF hO hD tau0 hKernel
    S L lambda delta Rstar p cover hd hRs hLam j y hy.2 hrceil Psi hPsi V hV u hCoverJ hPhys
  have hTrace:=nativePacketPhysicalHalfTrace_eq_on_overlap hF hO hD tau0 S L cover i j lambda hLam y hy r hrpos hrceil u
  rw [← hTrace] at hPj
  let U:Set R3 := ((cover.packet i).centers∩(cover.packet j).centers)∩{t:R3 | R t < cover.radiusCeiling}
  have hU:IsOpen U := ((cover.packet i).centers_open.inter (cover.packet j).centers_open).inter
    (isOpen_lt hR.continuous continuous_const)
  have hNear:nativeMixedKernelDensityFunctional hO hD tau0 S L (cover.packet i) lambda delta Rstar p Psi u=ᶠ[𝓝 y]
      nativeMixedKernelDensityFunctional hO hD tau0 S L (cover.packet j) lambda delta Rstar p Psi u := by
    filter_upwards [hU.mem_nhds (show y∈U from ⟨hy,hrceil⟩)] with t ht
    exact nativeMixedKernelDensityFunctional_eq_on_packet_overlap hO hD tau0 S L lambda delta Rstar p cover
      i j t ht.1 hd hRs hLam ht.2 Psi u
  have hScalar:=congrArg (fun a:ℝ => r*a)
    (normalizedSecondLaplacian_congr_of_eventuallyEq S.g1 S.g2 L lambda _ _ y hNear)
  have hPairEq:=hPi.symm.trans (hScalar.trans hPj)
  rw [hzEq]
  let test:=smoothHalfTrace hF hO hD tau0 (referencePhysicalPullbackData S.g1 S.g1_admissible L
    (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).native_data.1.1.1 lambda y r u)
  have hSamePair:sphereSobolevDualPairing (-(1/2:ℝ)) (op i) test=
      sphereSobolevDualPairing (-(1/2:ℝ)) (op j) test := by
    simpa only [op,test,r,R] using hPairEq
  change sphereSobolevDualPairing (-(1/2:ℝ)) (op i-op j) test=0
  simpa only [sphereSobolevDualPairing,inner_sub_left] using sub_eq_zero.mpr hSamePair

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
