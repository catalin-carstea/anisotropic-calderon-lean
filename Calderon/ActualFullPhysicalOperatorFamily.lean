import Calderon.ActualNativeFiniteCompressionFamily
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic SpectralCoreRegularity ActualFiniteHarmonicCore ReferenceDensityBounds
  EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConformalDepth
attribute [local irreducible] sphereSobolevInclusionL nativePacketPhysicalDensityOperator finiteCoreSobolevLift
  harmonicSphereSubspace sphereSobolevZeroEquiv

theorem exists_actual_full_physical_family_of_output_graphs
    (hcalc:FixedSobolevCalculus) (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L:ℝ) (cover:NativeNormalCover S L)
    (q delta Rstar:ℝ) (p:ℕ) (K:Set R3)
    (HOutput:∀ A:smoothCompactFiniteSphereCore hO hD,tsupport (A:R3→SphereL2)⊆K →
      ∃ f:R3→SphereL2,ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f⊆tsupport (A:R3→SphereL2) ∧
        ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
          sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (f y))=
          nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
            (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y):
    ∃ F:smoothCompactFiniteSphereCore hO hD→R3→SphereL2,
      ∀ A:smoothCompactFiniteSphereCore hO hD,tsupport (A:R3→SphereL2)⊆K →
      ContDiff ℝ ∞ (F A) ∧ HasCompactSupport (F A) ∧ tsupport (F A)⊆tsupport (A:R3→SphereL2) ∧
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (F A y))=
        nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
          (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y := by
  classical
  let F (A:smoothCompactFiniteSphereCore hO hD):R3→SphereL2:=
    if hA:tsupport (A:R3→SphereL2)⊆K then Classical.choose (HOutput A hA) else 0
  refine ⟨F,?_⟩
  intro A hA
  have hEq:F A=Classical.choose (HOutput A hA):=by
    dsimp only [F]
    exact dite_eq_left hA
  rw [hEq]
  exact Classical.choose_spec (HOutput A hA)

theorem exists_native_cover_uniform_actual_full_physical_operator_family
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L:ℝ) (hL:0 < L) (cover:NativeNormalCover S L)
    (hCenter:∀ i:Fin cover.count,∀ y∈(cover.packet i).centers,‖y-(cover.packet i).y0‖ < (cover.packet i).rho):
    ∃ p0:ℕ,2 ≤ p0 ∧ ∃ eps0:ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧
      ∀ p:ℕ,p0 ≤ p → ∀ q∈Icc (0:ℝ) cover.dilationCeiling,
      ∀ delta:ℝ,0 < delta → delta ≤ 1 → ∀ Rstar:ℝ,0 < Rstar →
      ∀ eps:ℝ,0 ≤ eps → eps ≤ eps0 → CurrentRadiusBootstrap S L q delta Rstar eps p →
      (∀ y∈cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling) ∧
      ∀ K:Set R3,K⊆interior cylinder →
      ∃ F:smoothCompactFiniteSphereCore hO hD→R3→SphereL2,
      ∀ A:smoothCompactFiniteSphereCore hO hD,tsupport (A:R3→SphereL2)⊆K →
      ContDiff ℝ ∞ (F A) ∧ HasCompactSupport (F A) ∧ tsupport (F A)⊆tsupport (A:R3→SphereL2) ∧
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (F A y))=
        nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
          (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y := by
  obtain ⟨p0,hp0,eps0,heps0,heps01,H⟩:=exists_native_cover_uniform_finite_core_physical_outputs
    hcalc hreg hF hO hD tau0 hKernel S L hL cover hCenter
  refine ⟨p0,hp0,eps0,heps0,heps01,?_⟩
  intro p hp q hq delta hd hd1 Rstar hRs eps heps heps0' hBoot
  obtain ⟨hRadius,HOut⟩:=H p hp q hq delta hd hd1 Rstar hRs eps heps heps0' hBoot
  refine ⟨hRadius,?_⟩
  intro K hK
  exact exists_actual_full_physical_family_of_output_graphs hcalc hF hO hD tau0 S L cover q delta Rstar p K
    (fun A hA=>HOut A (hA.trans hK))

theorem nativeFinitePhysicalCoerciveBound_iff_actual_full_family_lower_bound
    (hcalc:FixedSobolevCalculus) (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L:ℝ) (cover:NativeNormalCover S L)
    (chi:R3→ℝ) (hSupp:tsupport chi⊆interior cylinder) (q delta Rstar:ℝ) (p:ℕ) (c:ℝ)
    (F:smoothCompactFiniteSphereCore hO hD→R3→SphereL2)
    (hFData:∀ A:smoothCompactFiniteSphereCore hO hD,tsupport (A:R3→SphereL2)⊆tsupport chi →
      ContDiff ℝ ∞ (F A) ∧ HasCompactSupport (F A) ∧ tsupport (F A)⊆tsupport (A:R3→SphereL2) ∧
      ∀ i:Fin cover.count,∀ y∈interior cylinder∩(cover.packet i).centers,
        sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (F A y))=
        nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
          (finiteCoreSobolevLift hO hD (3/2:ℝ) A) i y):
    NativeFinitePhysicalCoerciveBound hcalc hF hO hD tau0 S L cover chi q delta Rstar p c ↔
      ∀ A:smoothCompactFiniteSphereCore hO hD,tsupport (A:R3→SphereL2)⊆tsupport chi →
      (∀ y:R3,sphereMean ((A:R3→SphereL2) y)=0) →
      c*(∫ y,referenceDensityFamily S.g1 L (q,y)*‖(A:R3→SphereL2) y‖^2) ≤
        ∫ y,referenceDensityFamily S.g1 L (q,y)*‖F A y‖^2 := by
  constructor
  · intro h A hA hMean
    exact h A hA hMean (F A) (hFData A hA).1 (hFData A hA).2.1
      ((hFData A hA).2.2.1.trans hA) (hFData A hA).2.2.2
  · intro h A hA hMean V _hV _hVc hVSupp hVGraph
    have hSame:F A=V:=eq_of_same_native_cover_negative_graph hO hD S L cover (tsupport chi) hSupp
      (F A) V ((hFData A hA).2.2.1.trans hA) hVSupp
      (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
        (finiteCoreSobolevLift hO hD (3/2:ℝ) A)) (hFData A hA).2.2.2 hVGraph
    have hLower:=h A hA hMean
    simpa only [hSame] using hLower

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
