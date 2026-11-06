import Calderon.ActualNativeConstantTestMean
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic SpectralCoreRegularity ActualFiniteHarmonicCore
  EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConformalDepth
  NativeSmoothSharpTraceCompletion NativeH2ThreeHalfValueTrace MetricVolume MetricOperator
  ActualNormalizedSecondMetricDrift ConnectionError
attribute [local irreducible] sphereSobolevInclusionL nativePacketPhysicalDensityOperator
  nativeMixedKernelDensityFunctional harmonicSphereSubspace

theorem nativePacketPhysicalDensityOperator_constant_pairing_eq_zero
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L lambda delta Rstar:ℝ) (p:ℕ) (cover:NativeNormalCover S L)
    (hd:0 < delta) (hRs:0 < Rstar) (hLam:lambda∈Icc (0:ℝ) cover.dilationCeiling)
    (i:Fin cover.count) (y:R3) (hy:y∈(cover.packet i).centers)
    (hrceil:referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (Psi:R3→SphereSobolev (3/2:ℝ)) (hPsi:ContDiff ℝ ∞ Psi)
    (hMean:∀ z:R3,sphereMean (nativeDensitySphereL2L hO hD (Psi z))=0):
    sphereSobolevDualPairing (-(1/2:ℝ))
      (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p Psi i y)
      (sphereSobolevConstantOne (1/2:ℝ))=0 := by
  let one:SmoothData:=⟨fun _ => (1:ℝ),contDiff_const⟩
  have hFunc:nativeMixedKernelDensityFunctional hO hD tau0 S L (cover.packet i)
      lambda delta Rstar p Psi one=(fun _ :R3=>0) := by
    funext z
    exact (nativeMixedKernelDensityFunctional_one_eq_sphereMean hO hD tau0 S L
      (cover.packet i) lambda delta Rstar p Psi z).trans (hMean z)
  have hPhys:∀ x∈(univ:Set R3),coordinateFluxDivergence
      (metricDivergenceFlux (fun z=>S.g1 (lambda • z)) one.1) x=0 := by
    intro x _
    simp [one,metricDivergenceFlux,coordinateFluxDivergence]
  have hP:=nativePacketPhysicalDensityOperator_pairing_physical_harmonic_test
    hcalc hreg hF hO hD tau0 hKernel S L lambda delta Rstar p cover hd hRs hLam
    i y hy hrceil Psi hPsi univ isOpen_univ one (subset_univ _) hPhys
  have hPullback:referencePhysicalPullbackData S.g1 S.g1_admissible L
      (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).native_data.1.1.1
      lambda y (referenceRadius delta Rstar p L y) one=one := by
    apply Subtype.ext
    funext z
    rfl
  rw [hPullback] at hP
  change _=sphereSobolevDualPairing (-(1/2:ℝ))
    (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p Psi i y)
    (smoothHalfTrace hF hO hD tau0 (⟨fun _ => (1:ℝ),contDiff_const⟩:SmoothData)) at hP
  rw [smoothHalfTrace_constant_one,hFunc] at hP
  have hZero:normalizedSecondLaplacian S.g1 S.g2 L lambda (fun _ :R3=>0) y=0 := by
    simp [normalizedSecondLaplacian,AngularPolynomial.densityWeightedDivergence]
  rw [hZero,mul_zero] at hP
  exact hP.symm

theorem sphereMean_eq_zero_of_native_cover_negative_graph
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (S:KnownSideSourceData) (L:ℝ) (cover:NativeNormalCover S L)
    (K:Set R3) (hK:K⊆interior cylinder)
    (V:R3→SphereL2) (hSupp:tsupport V⊆K)
    (Q:Fin cover.count→R3→SphereSobolev (-(1/2:ℝ)))
    (hGraph:∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (V y))=Q i y)
    (hQ:∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
      sphereSobolevDualPairing (-(1/2:ℝ)) (Q i y) (sphereSobolevConstantOne (1/2:ℝ))=0):
    ∀ y:R3,sphereMean (V y)=0 := by
  intro y
  by_cases hy:y∈K
  · obtain ⟨i,hi⟩:=cover.covers_cylinder y (interior_subset (hK hy))
    rw [← sphereSobolevDualPairing_L2_constantOne_eq_sphereMean hO hD (V y),
      hGraph i y ⟨hK hy,hi⟩]
    exact hQ i y ⟨hK hy,hi⟩
  · have hZero:V y=0:=image_eq_zero_of_notMem_tsupport (fun hh=>hy (hSupp hh))
    rw [hZero,map_zero]

theorem sphereMean_native_finite_physical_output_eq_zero
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L lambda delta Rstar:ℝ) (p:ℕ) (cover:NativeNormalCover S L)
    (hd:0 < delta) (hRs:0 < Rstar) (hLam:lambda∈Icc (0:ℝ) cover.dilationCeiling)
    (hRadius:∀ y∈interior cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (K:Set R3) (hK:K⊆interior cylinder)
    (A:smoothCompactFiniteSphereCore hO hD) (hMean:∀ y:R3,sphereMean ((A:R3→SphereL2) y)=0)
    (V:R3→SphereL2) (hSupp:tsupport V⊆K)
    (hGraph:∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (V y))=
      nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p
        (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y):
    ∀ y:R3,sphereMean (V y)=0 := by
  apply sphereMean_eq_zero_of_native_cover_negative_graph hO hD S L cover K hK V hSupp
    (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p
      (finiteCoreSobolevLift hO hD (3/2:ℝ) A)) hGraph
  intro i y hy
  apply nativePacketPhysicalDensityOperator_constant_pairing_eq_zero hcalc hreg hF hO hD tau0 hKernel
    S L lambda delta Rstar p cover hd hRs hLam i y hy.2 (hRadius y hy.1)
    (finiteCoreSobolevLift hO hD (3/2:ℝ) A)
    (finiteCoreSobolevLift_representation hO hD (3/2:ℝ) (by norm_num) A).1
  intro z
  rw [nativeDensitySphereL2L_finiteCoreSobolevLift]
  exact hMean z

theorem sphereMean_native_finite_compressed_physical_output_eq_zero
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L lambda delta Rstar:ℝ) (p:ℕ) (cover:NativeNormalCover S L)
    (hd:0 < delta) (hRs:0 < Rstar) (hLam:lambda∈Icc (0:ℝ) cover.dilationCeiling)
    (hRadius:∀ y∈interior cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (K:Set R3) (hK:K⊆interior cylinder)
    (A:smoothCompactFiniteSphereCore hO hD) (hMean:∀ y:R3,sphereMean ((A:R3→SphereL2) y)=0)
    (n:ℕ) (hn:1 ≤ n) (V:R3→SphereL2) (hSupp:tsupport V⊆K)
    (hGraph:∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (V y))=
      sphereSobolevPartialSumL (-(1/2:ℝ)) n
        (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p
          (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y)):
    ∀ y:R3,sphereMean (V y)=0 := by
  apply sphereMean_eq_zero_of_native_cover_negative_graph hO hD S L cover K hK V hSupp
    (fun i y=>sphereSobolevPartialSumL (-(1/2:ℝ)) n
      (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p
        (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y)) hGraph
  intro i y hy
  let f:=nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p
    (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y
  have hPair:=sphereSobolevDualPairing_partialSum_constantOne (-(1/2:ℝ)) n hn f
  have hPair':sphereSobolevDualPairing (-(1/2:ℝ)) (sphereSobolevPartialSumL (-(1/2:ℝ)) n f)
      (sphereSobolevConstantOne (1/2:ℝ))=
      sphereSobolevDualPairing (-(1/2:ℝ)) f (sphereSobolevConstantOne (1/2:ℝ)) := by
    convert hPair using 1 <;>
      simp [sphereSobolevConstantOne,sphereSobolevSingleL,SpectralWeightedGraph.besselWeight]
  refine hPair'.trans ?_
  apply nativePacketPhysicalDensityOperator_constant_pairing_eq_zero hcalc hreg hF hO hD tau0 hKernel
    S L lambda delta Rstar p cover hd hRs hLam i y hy.2 (hRadius y hy.1)
    (finiteCoreSobolevLift hO hD (3/2:ℝ) A)
    (finiteCoreSobolevLift_representation hO hD (3/2:ℝ) (by norm_num) A).1
  intro z
  rw [nativeDensitySphereL2L_finiteCoreSobolevLift]
  exact hMean z

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
